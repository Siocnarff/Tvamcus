package za.ac.up.tvamcus.runner

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.formulas.Literal
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import za.ac.up.tvamcus.encoders.*
import za.ac.up.tvamcus.logbook.TimeLog
import za.ac.up.tvamcus.print.printNoErrorFound
import za.ac.up.tvamcus.print.printSatisfiable
import za.ac.up.tvamcus.print.printState
import za.ac.up.tvamcus.print.printUnknown
import za.ac.up.tvamcus.parameters.PropertySpecification
import za.ac.up.tvamcus.sets.ConjunctiveSet
import za.ac.up.tvamcus.sets.DisjunctiveSet
import za.ac.up.tvamcus.state.cfgs.*
import za.ac.up.tvamcus.state.encoded.*
import java.util.*
import kotlin.math.pow


class Runner(propertySpecification: PropertySpecification, controlFlowGraphState: CFGS) {
    private val cfgs: CFGS = controlFlowGraphState
    private val propertySpec: PropertySpecification = propertySpecification
    private val templateTransitionSet: DisjunctiveSet<Transition> = cfgs.encodeAsTemplateTransitionSet()
    private val encodedPredicates: Set<String> = cfgs.deriveEncodedPredicates()

    /**
     * SAT-based k-bounded model checking runs from k = 0 to [bound]+1 and no SAT-optimisations activated
     */
    fun modelCheckNoOpt(bound: Int) {
        val stepResults = mutableListOf<Tristate>()
        val timestepCfgsFormulas = mutableListOf<Formula>()
        val timeLog = TimeLog()

        timestepCfgsFormulas.add(init())
        for (t in 0 until bound + 1) {
            val propertyFormula = if (propertySpec.type == "liveness") livenessViolationProperty(t) else errorLocation(propertySpec.location, t)
            print(" k(a)=$t")
            timeLog.startLap()
            stepResults.add(
                timestepCfgsFormulas.evaluateLatestConjunctedWith(property = propertyFormula, literal = "unknown")
            )
            timeLog.endLap()
            printState(
                timeLog.lastLapTime(),
                stepResults.last().toString()
            )
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = solver.model().literals().pathInfo(t)
                print(" k(b)=$t")
                timeLog.startLap()
                stepResults.add(
                    timestepCfgsFormulas.evaluateLatestConjunctedWith(property = propertyFormula, literal = "~unknown")
                )
                timeLog.endLap()
                printState(
                    timeLog.lastLapTime(),
                    stepResults.last().toString()
                )
                if (stepResults.last() == Tristate.TRUE) {
                    println("\nError Path")
                    solver.model().literals().pathInfo(t).print()
                    printSatisfiable(
                        time =timeLog.totalTime(),
                        timestep = t
                    )
                    if(propertySpec.doubleTest) {
                        timestepCfgsFormulas.last().solveAgainWithConstraint(pathFormula(solver.model().literals().pathInfo(t)), t, bound)
                    }
                } else {
                    pathInfo.print()
                    printUnknown(
                        time = timeLog.totalTime(),
                        timestep = t
                    )
                    if(propertySpec.doubleTest) {
                        timestepCfgsFormulas.last().solveAgainWithConstraint(pathFormula(pathInfo), t, bound)
                    }

                }
                return
            }
            timestepCfgsFormulas.add(ff.and(timestepCfgsFormulas.last(), transitionSetAsFormula(t)))
        }
        timeLog.endLap()
        printNoErrorFound(timeLog.totalTime(), bound)
    }

    private fun MutableList<Formula>.evaluateLatestConjunctedWith(property: Formula, literal: String): Tristate {
        solver.reset()
        solver.add(ff.and(this.last(), property, p.parse(literal)))
        return solver.sat()
    }

    /**
     * Experimental function
     */
    private fun Formula.solveAgainWithConstraint(constraint: Formula, startIndex: Int, bound: Int) {
        println("\n=============================================================================")
        println("============= Solving Again with constraint - restarting timer ==============")
        println("=============================================================================\n")
        val stepResults = mutableListOf<Tristate>()
        val timeLog = TimeLog()
        val formulas = mutableListOf<Formula>()
        formulas.add(ff.and(this, constraint))
        for (t in startIndex until bound + 1) {
            val propertyFormula = if (propertySpec.type == "liveness") livenessViolationProperty(t) else errorLocation(propertySpec.location, t)
            print(" k(a)=$t")
            timeLog.startLap()
            stepResults.add(
                formulas.evaluateLatestConjunctedWith(property = propertyFormula, literal = "unknown")
            )
            timeLog.endLap()
            printState(
                timeLog.lastLapTime(),
                stepResults.last().toString()
            )
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = solver.model().literals().pathInfo(t)
                print(" k(b)=$t")
                timeLog.startLap()
                stepResults.add(
                    formulas.evaluateLatestConjunctedWith(property = propertyFormula, literal = "~unknown")
                )
                timeLog.endLap()
                printState(
                    timeLog.lastLapTime(),
                    stepResults.last().toString()
                )
                if (stepResults.last() == Tristate.TRUE) {
                    println("\nError Path")
                    solver.model().literals().pathInfo(t).print()
                    printSatisfiable(
                        timeLog.lastLapTime(),
                        timestep = t
                    )
                } else {
                    pathInfo.print()
                    printUnknown(
                        timeLog.lastLapTime(),
                        timestep = t
                    )
                }
                return
            }
            formulas.add(ff.and(formulas.last(), transitionSetAsFormula(timestep = t)))
        }
    }

    /**
     * Creates timestep specific formula from [templateTransitionSet]
     *
     * This is an encoded timestep specific formula of the [cfgs]
     *
     * @param timestep timestep to create formula for
     * @return the encoded [cfgs] formula for timestep [timestep]
     */
    private fun transitionSetAsFormula(timestep: Int): Formula {
        val bigOr = mutableSetOf<Formula>()
        templateTransitionSet.disjoinOver.forEach{ bigOr.add( it.asFormula(timestep) ) }
        return ff.or(bigOr)
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
        val core = ff.and(
            oldLocation.asFormula(timestep),
            operation.asFormula(timestep),
            newLocation.asFormula(timestep),
            idle.asConjunctiveFormula(timestep)
        )
        return if(propertySpec.type == "liveness") {
            ff.and(core, livenessEvaluationFormula(parentProcess, timestep))
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
        return ff.and(
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
        return if(!propertySpec.fairnessON) {
            conjunctiveSet.asConjunctiveFormula(timestep)
        } else {
            ff.and(
                conjunctiveSet.asConjunctiveFormula(timestep),
                fairnessConstraintFormula(lId, timestep)
            )
        }
    }

    private fun ConjunctiveSet<String>.asConjunctiveFormula(timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        conjunctOver.forEach{ bigAnd.add(it.asFormula(timestep)) }
        return ff.and(bigAnd)
    }

    private fun fairnessConstraintFormula(lId: Int, timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        bigAnd.add("(fr_I_${lId} <=> (re_i | rd_i))".asFormula(timestep))
        for(pId in cfgs.processes.indices.filterNot{ it == lId }) {
            bigAnd.add(p.parse("(fr_${timestep + 1}_${pId} <=> fr_${timestep}_${pId})"))
        }
        return ff.and(bigAnd)
    }

    private fun String.asFormula(t: Int): Formula {
        return p.parse(this.insertTimestep(t))
    }

    /**
     * by Definitions 13 and 14 in SCP20
     */
    private fun encStateRecording(): ConjunctiveSet<String> {
        val bigAnd = mutableSetOf<String>()
        bigAnd.add("(rd_I <=> (re_i | rd_i))")
        encodedPredicates.distinct().forEach {
            bigAnd.add(
                "(${it.replace("i", "I")}_c <=> (((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
            )
        }
        bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${propertySpec.processList.encProgressExpression()})))")
        return ConjunctiveSet(bigAnd)
    }

    /**
     * Encodes predicate expression "progress" over list of locations that will be used in liveness checking FG(not(progress))
     *
     * by Definitions 13 and 14 in SCP20
     *
     * @return Encoding of predicate expression "progress" in unparsed string format
     */
    private fun List<Int>.encProgressExpression(): String {
        var progress = ""
        for (pId in this) {
            progress += cfgs.encLocation(pId, lId = propertySpec.location)
            progress += " ${propertySpec.operator} "
        }
        return progress.dropLast(3)
    }

    /**
     * Initializes formula used in [modelCheckNoOpt]
     *
     * see page 45 of SCP19
     *
     * @return initial state of [cfgs], encoded to formula
     */
    private fun init(): Formula {
        val conjunctOver = mutableListOf<Formula>()
        for (pId in cfgs.processes.indices) {
            conjunctOver.add(p.parse(cfgs.encLocation(pId, lId = 0, timestep = "0")))
            if (propertySpec.type == "liveness") {
                conjunctOver.add(p.parse("~rd_0 & ~lv_0"))
                conjunctOver.add(p.parse(cfgs.encLocationCopy(pId, lId = 0, timestep = "0")))
                if(propertySpec.fairnessON) {
                    conjunctOver.add(p.parse("~fr_0_${pId}"))
                }
            }
        }
        for (predicate in cfgs.predicates) {
            val initAs: Boolean? = cfgs.init[predicate.key]
            conjunctOver.add(
                if (initAs != null && !initAs) {
                    p.parse(encIsFalse(predicate.value, timestep = "0"))
                } else {
                    p.parse(encIsTrue(predicateId = predicate.value, timestep = "0"))
                }
            )
            if(propertySpec.type == "liveness") {
                conjunctOver.add(
                    if (initAs != null && !initAs) {
                        p.parse(encIsFalseCopy(predicateId = predicate.value, timestep = "0"))
                    } else {
                        p.parse(encIsTrueCopy(predicateId = predicate.value, timestep = "0"))
                    }
                )
            }
        }
        return ff.and(conjunctOver)
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
            toJoin.add(p.parse(cfgs.encLocation(pId, lId, timestep.toString())))
        }
        return if (propertySpec.operator == "|") ff.or(toJoin) else ff.and(toJoin)
    }

    /**
     * Creates liveness property evaluation formula
     *
     * by Definition 14 in SCP20
     *
     * Encodes that a loop has been found at timestep [timestep]] in the state space of [cfgs] that violates liveness
     * (under fairness if and only if [PropertySpecification.fairnessON])
     *
     * @param [timestep] the timestep at which the loop closes
     * @return liveness violation property evaluation formula to be added to formula for [timestep] of [templateTransitionSet]
     */
    private fun livenessViolationProperty(timestep: Int): Formula {
        val bigAnd = mutableSetOf<Formula>()
        bigAnd.add(p.parse("rd_$timestep"))
        encodedPredicates.forEach { bigAnd.add(p.parse("(${it.insertTimestep(timestep)} <=> ${it.insertTimestep(timestep)}_c)")) }
        bigAnd.add(p.parse("~lv_$timestep"))
        if(propertySpec.fairnessON) {
            for(pId in cfgs.processes.indices) {
                bigAnd.add(p.parse("fr_${timestep}_$pId"))
            }
        }
        return ff.and(bigAnd)
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

    /**
     * Ascertains the truth value of the variables re_i and rd_i in the SortedSet of literals
     * it is called on (this Set should be derived from the SAT model)
     *
     * @param [timestep] used to create the correct instance of re_i and rd_i
     * @return Pair<statusOf(re_[timestep]), statusOf(rd_[timestep])>
     */
    private fun SortedSet<Literal>.reRdEvaluation(timestep: Int): Pair<String, String> {
        return Pair(
            if (this.contains(ff.literal("re_$timestep", true))) "re = true" else "re = false",
            if (this.contains(ff.literal("rd_$timestep", true))) "rd = true" else "rd = false"
        )
    }

    /**
     * For the [timestep] timestep encoding of each predicate in the [cfgs], ascertain the truth value of said predicate
     * in the SortedSet of literals it is called on (this Set should be derived from the SAT model)
     *
     * @param [timestep] timestep to check predicate truth values
     * @return list of predicates and their respective truth values
     */
    private fun SortedSet<Literal>.predicateEvaluation(timestep: Int): MutableList<String> {
        val predicateStatuses = mutableListOf<String>()
        for(p in cfgs.predicates) {
            if(this.contains(ff.literal("${p.value}_${timestep}_u", true))) {
                predicateStatuses.add("${p.key} = unknown")
            } else if(this.contains(ff.literal("${p.value}_${timestep}_t", true))) {
                predicateStatuses.add("${p.key} = true")
            } else {
                predicateStatuses.add("${p.key} = false")
            }
        }
        return predicateStatuses
    }

    /**
     * Ascertains the truth value of the fairness evaluation variable of each process (fr_i_pId)
     * in the SortedSet of literals it is called on (this Set should be derived from the SAT model)
     *
     * @param [timestep] used to create the correct instance of fr_i_pId
     * @return List of process fairness variable truth values
     */
    private fun SortedSet<Literal>.fairnessEvaluation(timestep: Int): MutableList<String> {
        val fairnessVariableStatuses = mutableListOf<String>()
        if(!propertySpec.fairnessON) {
            fairnessVariableStatuses.add("n.a.")
            return fairnessVariableStatuses
        }
        for(pId in cfgs.processes.indices) {
            if(this.contains(ff.literal("fr_${timestep}_${pId}", true))) {
                fairnessVariableStatuses.add("P$pId = fair")
            } else {
                fairnessVariableStatuses.add("P$pId = unfair")
            }
        }
        return fairnessVariableStatuses
    }

    /**
     * Using the SortedSet of literals it is called on, it derives from the truth values of the location literals, where each process is at timestep [timestep]
     * @param [timestep] timestep to find process locations for
     * @return list of strings denoting the timestep [timestep] location of each process
     */
    private fun SortedSet<Literal>.locationEvaluation(timestep: Int): MutableList<String> {
        val processLocations = mutableListOf<String>()
        for ((pId, process) in cfgs.processes.withIndex()) {
            var processLocation = ""
            for(d in 0 until digitRequired(process.numberOfLocations())) {
                processLocation += if(this.contains(ff.literal("n_${timestep}_${pId}_${d}", false))) {
                    "0"
                } else {
                    "1"
                }
            }
            processLocations.add(processLocation)
        }
        return processLocations
    }

    private data class State(
        val timestep: Int,
        val locationStatus: MutableList<String>,
        val predicateStatus: MutableList<String>,
        val fairnessStatus: MutableList<String>,
        val reRdStatus: Pair<String, String>
    )

    private fun SortedSet<Literal>.pathInfo(bound: Int): MutableList<State> {
        val steps = mutableListOf<State>()
        for(k in 0 until bound + 1) {
            steps.add(
                State(
                    k,
                    this.locationEvaluation(k),
                    this.predicateEvaluation(k),
                    this.fairnessEvaluation(k),
                    this.reRdEvaluation(k)
                )
            )

        }
        return steps
    }

    /**
     * Experimental function
     */
    private fun pathFormula(steps: MutableList<State>): Formula {
        val bigAnd = mutableSetOf<Formula>()
        for((t, step) in steps.withIndex()) {
            for((pId, location) in step.locationStatus.withIndex()) {
                bigAnd.add(
                    p.parse(cfgs.encLocation(pId, lId = location.toInt(), timestep = t.toString()))
                )
            }
        }
        return ff.and(bigAnd)
    }

    private fun String.toInt(): Int {
        var tally = 0
        for((index, c) in this.reversed().withIndex()) {
            tally += when (c) {
                '1' -> (2.0.pow(index)).toInt()
                '0' -> 0
                else -> throw error("String contains invalid characters, only 1, or 0 allowed.")
            }
        }
        return tally
    }

    private fun MutableList<State>.print() {
        this.forEachIndexed { index, stepStat ->
            println("\n$index:")
            println(stepStat.locationStatus)
            println(stepStat.predicateStatus)
            println(stepStat.fairnessStatus)
            println(stepStat.reRdStatus)
        }
    }

    companion object {
        private val ff = FormulaFactory()
        private val p = PropositionalParser(ff)
        private val solver: MiniSat = MiniSat.glucose(ff)
    }
}