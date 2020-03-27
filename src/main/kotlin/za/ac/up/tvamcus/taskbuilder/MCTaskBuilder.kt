package za.ac.up.tvamcus.taskbuilder

import org.logicng.formulas.Formula
import za.ac.up.tvamcus.encoders.*
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.disjoin
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.sets.ConjunctiveSet
import za.ac.up.tvamcus.sets.DisjunctiveSet
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.state.cfgs.CfgsTransition
import za.ac.up.tvamcus.state.encoded.Operation
import za.ac.up.tvamcus.state.encoded.Transition

class MCTaskBuilder(propertySpecification: PropertySpecification, controlFlowGraphState: CFGS) {
    private val cfgs: CFGS = controlFlowGraphState
    private val propertySpec: PropertySpecification = propertySpecification
    private val templateTransitionSet: DisjunctiveSet<Transition> = cfgs.encodeAsTemplateTransitionSet()
    private val encodedPredicates: Set<String> = cfgs.deriveEncodedPredicates()
    val initialState: Formula = init()

    /**
     * Creates timestep specific formula from [templateTransitionSet]
     *
     * This is an encoded timestep specific formula of the [cfgs]
     *
     * @param timestep timestep to create formula for
     * @return the encoded [cfgs] formula for timestep [timestep]
     */
    fun cfgAsFormula(timestep: Int): Formula {
        val bigOr = mutableSetOf<Formula>()
        templateTransitionSet.disjoinOver.forEach{ bigOr.add( it.asFormula(timestep) ) }
        return disjoin(bigOr)
    }

    /**
     * Initializes formula
     *
     * see page 45 of SCP19
     *
     * @return initial state of [cfgs], encoded to formula
     */
    private fun init(): Formula {
        val over = mutableListOf<Formula>()
        for (pId in cfgs.processes.indices) {
            over.add(parse(cfgs.encLocation(pId, lId = 0, t = "0")))
            if (propertySpec.type == "liveness") {
                over.add(parse("~rd_0 & ~lv_0"))
                over.add(parse(cfgs.encLocationCopy(pId, lId = 0, t = "0")))
                if(propertySpec.fairnessOn) {
                    over.add(parse("~fr_0_${pId}"))
                }
            }
        }
        for (predicate in cfgs.predicates) {
            val initAs: Boolean? = cfgs.init[predicate.key]
            over.add(
                if (initAs != null && !initAs) {
                    parse(encIsFalse(predicate.value, t = "0"))
                } else {
                    parse(encIsTrue(predicateId = predicate.value, t = "0"))
                }
            )
            if(propertySpec.type == "liveness") {
                over.add(
                    if (initAs != null && !initAs) {
                        parse(encIsFalseCopy(predicateId = predicate.value, t = "0"))
                    } else {
                        parse(encIsTrueCopy(predicateId = predicate.value, t = "0"))
                    }
                )
            }
        }
        return conjunct(over)
    }

    fun propertyFormula(t: Int): Formula {
        return  if (propertySpec.type == "liveness") {
            livenessViolationProperty(t)
        } else {
            errorLocation(propertySpec.location, t)
        }

    }
    /**
     * Creates timestep specific formula from the [Transition] it is called on
     *
     * Note, [PropertySpecification.type] is also taken into account when encoding the [Transition]
     *
     * @param [timestep] timestep to encode [Transition] for
     * @return encoded formula of the [Transition]
     */
    private fun Transition.asFormula(timestep: Int): Formula {
        val core = conjunct(
            oldLocation.asFormula(timestep),
            operation.asFormula(timestep),
            newLocation.asFormula(timestep),
            idle.asConjunctiveFormula(timestep)
        )
        return if(propertySpec.type == "liveness") {
            conjunct(core, livenessEvaluationFormula(parentProcess, timestep))
        } else {
            core
        }
    }

    /**
     * Creates timestep specific sub-formula from [Operation] it is called on
     *
     * @param timestep timestep to create sub-formula for
     * @return the encoded [cfgs] sub-formula for timestep [timestep]
     */
    private fun Operation.asFormula(timestep: Int): Formula {
        return conjunct(
            guard.asFormula(timestep),
            assignments.asConjunctiveFormula (timestep)
        )
    }

    /**
     * Creates the liveness location encoding of the Int it is called on
     *
     * by Definitions 13 and 14 in SCP20
     *
     * @param timestep timestep formula is to be created for
     * @return [Formula] to conjunct with the encoding of each [CfgsTransition] when testing liveness
     */
    private fun livenessEvaluationFormula(lId: Int, timestep: Int): Formula {
        val conjunctiveSet = encStateRecording()
        return if(!propertySpec.fairnessOn) {
            conjunctiveSet.asConjunctiveFormula(timestep)
        } else {
            conjunct(
                conjunctiveSet.asConjunctiveFormula(timestep),
                fairnessConstraintFormula(lId, timestep)
            )
        }
    }

    private fun ConjunctiveSet<String>.asConjunctiveFormula(timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        conjunctOver.forEach{ bigAnd.add(it.asFormula(timestep)) }
        return conjunct(bigAnd)
    }

    private fun fairnessConstraintFormula(lId: Int, timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        bigAnd.add("(fr_I_${lId} <=> (re_i | rd_i))".asFormula(timestep))
        for(pId in cfgs.processes.indices.filterNot{ it == lId }) {
            bigAnd.add(parse("(fr_${timestep + 1}_${pId} <=> fr_${timestep}_${pId})"))
        }
        return conjunct(bigAnd)
    }

    private fun String.asFormula(t: Int): Formula {
        return parse(this.insertTimestep(t))
    }

    /**
     * by Definitions 13 and 14 in SCP20
     */
    private fun encStateRecording(): ConjunctiveSet<String> {
        val bigAnd = mutableSetOf<String>()
        bigAnd.add("(rd_I <=> (re_i | rd_i))")
        encodedPredicates.distinct().forEach {
            bigAnd.add(
                "(${it.replace("i", "I")}_c <=> " +
                        "(((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
            )
        }
        bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${encProgressExpression(propertySpec.processList)})))")
        return ConjunctiveSet(bigAnd)
    }

    /**
     * Encodes predicate expression "progress" over list of locations
     * that will be used in liveness checking FG(not(progress))
     *
     * by Definitions 13 and 14 in SCP20
     *
     * @return Encoding of predicate expression "progress" in unparsed string format
     */
    private fun encProgressExpression(processIds: List<Int>): String {
        var progress = ""
        for (pId in processIds) {
            progress += cfgs.encLocation(pId, lId = propertySpec.location)
            progress += " ${propertySpec.operator} "
        }
        return progress.dropLast(3)
    }

    /**
     * Encodes the location it is called on as a part of the composite error location for timestep [timestep]
     *
     * by Definition 8 in SPC19
     *
     * @param timestep timestep for which location is deemed as the error location
     * @return formula of error location for timestep [timestep]
     */
    private fun errorLocation(lId: Int, timestep: Int): Formula {
        val toJoin = mutableListOf<Formula>()
        for (pId in propertySpec.processList) {
            toJoin.add(parse(cfgs.encLocation(pId, lId, timestep.toString())))
        }
        return if (propertySpec.operator == '|') disjoin(toJoin) else conjunct(toJoin)
    }

    /**
     * Creates liveness property evaluation formula
     *
     * by Definition 14 in SCP20
     *
     * Encodes that a loop has been found at timestep [timestep]] in the state space of [cfgs] that violates liveness
     * (under fairness if and only if [PropertySpecification.fairnessOn])
     *
     * @param [timestep] the timestep at which the loop closes
     * @return liveness violation property evaluation formula to
     * be added to formula for [timestep] of [templateTransitionSet]
     */
    private fun livenessViolationProperty(timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        bigAnd.add(parse("rd_$timestep"))
        encodedPredicates.forEach {
            bigAnd.add(parse("(${it.insertTimestep(timestep)} <=> ${it.insertTimestep(timestep)}_c)"))
        }
        bigAnd.add(parse("~lv_$timestep"))
        if(propertySpec.fairnessOn) {
            for(pId in cfgs.processes.indices) {
                bigAnd.add(parse("fr_${timestep}_$pId"))
            }
        }
        return conjunct(bigAnd)
    }

    /**
     * Replaces i in the string it is called on with [timestep] and I with ([timestep] + 1)
     *
     * @param timestep base timestep to insert into string
     * @return string with [timestep] inserted where placeholders were
     */
    private fun String.insertTimestep(timestep: Int): String {
        return this.replace(
            "i", "$timestep"
        ).replace(
            "I", "${timestep + 1}"
        )
    }
}