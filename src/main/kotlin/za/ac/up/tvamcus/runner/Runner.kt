package za.ac.up.tvamcus.runner

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.formulas.Literal
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import za.ac.up.tvamcus.encoders.*
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
    private val propertySpecification: PropertySpecification = propertySpecification
    private val templateTransitionSet: DisjunctiveSet<Transition> = encodeTemplateTransitionSet(cfgs)
    private val encodedPredicates: List<String> = derivePredicates(cfgs)

    /**
     * Encodes all possible state space Transitions from i to I
     *
     * This encoding is stored in [templateTransitionSet]
     *
     * by Definition 11 in SCP19
     */
    private fun encodeTemplateTransitionSet(cfgs: CFGS): DisjunctiveSet<Transition> {
        val over: MutableList<Transition> = mutableListOf()
        for((pId, process) in cfgs.processes.withIndex()) {
            for (transition in process.transitions) {
                over.add(
                    cfgs.encTransition(pId, transition)
                )
            }
        }
        println("...CFGSEncoded")
        return DisjunctiveSet(over)
    }

    /**
     * Derives the full list of predicates that are in [templateTransitionSet] and adds them to [encodedPredicates] for future use
     */
    private fun derivePredicates(cfgs: CFGS): List<String> {
        val predicates: MutableList<String> = mutableListOf()
        for (p in cfgs.predicates) {
            predicates.add("${p.value}_i_u")
            predicates.add("${p.value}_i_t")
        }
        for ((pId, process) in cfgs.processes.withIndex()) {
            for (d in 0 until digitRequired(process.numberOfLocations())) {
                predicates.add("n_i_${pId}_${d}")
            }
        }
        return predicates
    }

    /**
     * SAT-based k-bounded model checking runs from k = 0 to [bound]+1 and no SAT-optimisations activated
     */
    fun modelCheckNoOpt(bound: Int) {
        val performanceLog = mutableListOf<Long>()
        val stepResults = mutableListOf<Tristate>()
        val startTime = System.nanoTime()
        var formula = init()
        for (t in 0 until bound + 1) {
            val propertyFormula = if (propertySpecification.type == "liveness") livenessViolationProperty(t) else errorLocation(propertySpecification.location, t)
            print(" k(a)=$t")
            val unitStartTimeA = System.nanoTime()
            solver.reset()
            solver.add(ff.and(formula, propertyFormula, p.parse("unknown")))
            stepResults.add(solver.sat())
            performanceLog.add(System.nanoTime() - unitStartTimeA)
            printState(
                performanceLog.last(),
                stepResults.last().toString()
            )
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = solver.model().literals().pathInfo(t)
                print(" k(b)=$t")
                val unitStartTimeB = System.nanoTime()
                solver.reset()
                solver.add(
                    ff.and(formula, propertyFormula, p.parse("~unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeB)
                printState(
                    performanceLog.last(),
                    stepResults.last().toString()
                )
                if (stepResults.last() == Tristate.TRUE) {
                    val time = System.nanoTime()
                    println("\nError Path")
                    solver.model().literals().pathInfo(t).print()
                    printSatisfiable(
                        startT = startTime,
                        endT = time,
                        timestep = t
                    )
                    if(propertySpecification.doubleTest) {
                        formula.solveAgainWithConstraint(pathFormula(solver.model().literals().pathInfo(t)), t, bound)
                    }
                } else {
                    val time = System.nanoTime()
                    pathInfo.print()
                    printUnknown(
                        startT = startTime,
                        endT = time,
                        timestep = t
                    )
                    if(propertySpecification.doubleTest) {
                        formula.solveAgainWithConstraint(pathFormula(pathInfo), t, bound)
                    }

                }

                return
            }
            formula = ff.and(formula, formulaForTimestamp(t))
        }
        printNoErrorFound(startTime, System.nanoTime(), bound)
    }

    /**
     * Experimental function
     */
    private fun Formula.solveAgainWithConstraint(constraint: Formula, startIndex: Int, bound: Int) {
        println("\n=============================================================================")
        println("============= Solving Again with constraint - restarting timer ==============")
        println("=============================================================================\n")
        val performanceLog = mutableListOf<Long>()
        val stepResults = mutableListOf<Tristate>()
        val startTime = System.nanoTime()
        var formula = ff.and(this, constraint)
        for (t in startIndex until bound + 1) {
            val property = if (propertySpecification.type == "liveness") livenessViolationProperty(t) else errorLocation(propertySpecification.location, t)
            print(" k(a)=$t")
            val unitStartTimeA = System.nanoTime()
            solver.reset()
            solver.add(ff.and(formula, property, p.parse("unknown")))
            stepResults.add(solver.sat())
            performanceLog.add(System.nanoTime() - unitStartTimeA)
            printState(
                performanceLog.last(),
                stepResults.last().toString()
            )
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = solver.model().literals().pathInfo(t)
                print(" k(b)=$t")
                val unitStartTimeB = System.nanoTime()
                solver.reset()
                solver.add(
                    ff.and(formula, property, p.parse("~unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeB)
                printState(
                    performanceLog.last(),
                    stepResults.last().toString()
                )
                if (stepResults.last() == Tristate.TRUE) {
                    val time = System.nanoTime()
                    println("\nError Path")
                    solver.model().literals().pathInfo(t).print()
                    printSatisfiable(
                        startT = startTime,
                        endT = time,
                        timestep = t
                    )
                } else {
                    val time = System.nanoTime()
                    pathInfo.print()
                    printUnknown(
                        startT = startTime,
                        endT = time,
                        timestep = t
                    )
                }
                return
            }
            formula = ff.and(formula, formulaForTimestamp(t))
        }
    }

    /**
     * Creates timestep specific formula from [templateTransitionSet]
     *
     * This is an encoded timestep specific formula of the [cfgs]
     *
     * @param t timestep to create formula for
     * @return the encoded [cfgs] formula for timestep [t]
     */
    private fun formulaForTimestamp(t: Int): Formula {
        val bigOr: MutableList<Formula> = mutableListOf()
        templateTransitionSet.disjoinOver.forEach{ bigOr.add( it.asFormula(t)) }
        return ff.or(bigOr)
    }
    /**
     * Creates timestep specific formula from the [CfgsTransition] it is called on
     *
     * Note, [PropertySpecification.type] is also taken into account when encoding the [CfgsTransition]
     *
     * @param [t] timestep to encode [CfgsTransition] for
     * @return encoded formula of the [CfgsTransition]
     */
    private fun Transition.asFormula(timestamp: Int): Formula {
        val core = ff.and(
            oldLocation.asFormula(timestamp),
            operation.asFormula(timestamp),
            newLocation.asFormula(timestamp),
            idle.asConjunctiveFormula(timestamp)
        )
        return if(propertySpecification.type == "liveness") {
            ff.and(core, livenessEvaluationFormula(parentProcess, timestamp))
        } else {
            core
        }
    }

    /**
     * Creates timestep specific sub-formula from [Operation] it is called on
     *
     * @param t timestep to create sub-formula for
     * @return the encoded [cfgs] sub-formula for timestep [t]
     */
    private fun Operation.asFormula(t: Int): Formula {
        return ff.and(
            guard.asFormula(t),
            assignments.asConjunctiveFormula ( t )
        )
    }

    /**
     * Creates the liveness location encoding of the Int it is called on
     *
     * by Definitions 13 and 14 in SCP20
     *
     * @param t timestep formula is to be created for
     * @return [Formula] to conjunct with the encoding of each [CfgsTransition] when testing liveness
     */
    private fun livenessEvaluationFormula(lId: Int, t: Int): Formula {
        val conjunctiveSet = encStateRecording()
        return if(!propertySpecification.fairnessON) {
            conjunctiveSet.asConjunctiveFormula(t)
        } else {
            ff.and(
                conjunctiveSet.asConjunctiveFormula(t),
                fairnessConstraintFormula(lId, t)
            )
        }
    }
    private fun ConjunctiveSet<String>.asConjunctiveFormula(timestamp: Int): Formula {
        val bigAnd: MutableList<Formula> = mutableListOf()
        conjunctOver.forEach{ bigAnd.add(it.asFormula(timestamp)) }
        return ff.and(bigAnd)
    }
    private fun fairnessConstraintFormula(lId: Int, t: Int): Formula {
        val bigAnd = mutableListOf<Formula>()
        bigAnd.add("(fr_I_${lId} <=> (re_i | rd_i))".asFormula(t))
        for(pId in cfgs.processes.indices.filterNot{ it == lId }) {
            bigAnd.add(p.parse("(fr_${t + 1}_${pId} <=> fr_${t}_${pId})"))
        }
        return ff.and(bigAnd)
    }

    /**
     * by Definitions 13 and 14 in SCP20
     */
    private fun encStateRecording(): ConjunctiveSet<String> {
        val bigAnd = mutableListOf<String>()
        bigAnd.add("(rd_I <=> (re_i | rd_i))")
        encodedPredicates.distinct().forEach {
            bigAnd.add(
                "(${it.replace("i", "I")}_c <=> (((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
            )
        }
        bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${propertySpecification.processList.encProgressExpression()})))")
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
            progress += cfgs.encLocation(pId, lId = propertySpecification.location)
            progress += " ${propertySpecification.operator} "
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
            if (propertySpecification.type == "liveness") {
                conjunctOver.add(p.parse("~rd_0 & ~lv_0"))
                conjunctOver.add(p.parse(cfgs.encLocationCopy(pId, lId = 0, timestep = "0")))
                if(propertySpecification.fairnessON) {
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
            if(propertySpecification.type == "liveness") {
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
     * Encodes the location it is called on as a part of the composite error location for timestep [t]
     *
     * by Definition 8 in SPC19
     *
     * @param t timestep for which location is deemed as the error location
     * @return formula of error location for timestep [t]
     */
    private fun errorLocation(lId: Int, t: Int): Formula {
        val toJoin = mutableListOf<Formula>()
        for (pId in propertySpecification.processList) {
            toJoin.add(p.parse(cfgs.encLocation(pId, lId, timestep = t.toString())))
        }
        return if (propertySpecification.operator == "|") ff.or(toJoin) else ff.and(toJoin)
    }

    /**
     * Creates liveness property evaluation formula
     *
     * by Definition 14 in SCP20
     *
     * Encodes that a loop has been found at timestep [t] in the state space of [cfgs] that violates liveness
     * (under fairness if and only if [PropertySpecification.fairnessON])
     *
     * @param [t] the timestep at which the loop closes
     * @return liveness violation property evaluation formula to be added to formula for [t] of [templateTransitionSet]
     */
    private fun livenessViolationProperty(t: Int): Formula {
        val bigAnd = mutableListOf<Formula>()
        bigAnd.add(p.parse("rd_$t"))
        encodedPredicates.forEach { bigAnd.add(p.parse("(${it.insertTimestamp(t)} <=> ${it.insertTimestamp(t)}_c)")) }
        bigAnd.add(p.parse("~lv_$t"))
        if(propertySpecification.fairnessON) {
            for(pId in cfgs.processes.indices) {
                bigAnd.add(p.parse("fr_${t}_$pId"))
            }
        }
        return ff.and(bigAnd)
    }

    /**
     * Ascertains the truth value of the variables re_i and rd_i in the SortedSet of literals
     * it is called on (this Set should be derived from the SAT model)
     *
     * @param [t] used to create the correct instance of re_i and rd_i
     * @return Pair<statusOf(re_[t]), statusOf(rd_[t])>
     */
    private fun SortedSet<Literal>.reRdEvaluation(t: Int): Pair<String, String> {
        return Pair(
            if (this.contains(ff.literal("re_$t", true))) "re = true" else "re = false",
            if (this.contains(ff.literal("rd_$t", true))) "rd = true" else "rd = false"
        )
    }

    /**
     * For the [t] timestep encoding of each predicate in the [cfgs], ascertain the truth value of said predicate
     * in the SortedSet of literals it is called on (this Set should be derived from the SAT model)
     *
     * @param [t] timestep to check predicate truth values
     * @return list of predicates and their respective truth values
     */
    private fun SortedSet<Literal>.predicateEvaluation(t: Int): MutableList<String> {
        val predicateStatuses = mutableListOf<String>()
        for(p in cfgs.predicates) {
            if(this.contains(ff.literal("${p.value}_${t}_u", true))) {
                predicateStatuses.add("${p.key} = unknown")
            } else if(this.contains(ff.literal("${p.value}_${t}_t", true))) {
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
     * @param [t] used to create the correct instance of fr_i_pId
     * @return List of process fairness variable truth values
     */
    private fun SortedSet<Literal>.fairnessEvaluation(t: Int): MutableList<String> {
        val fairnessVariableStatuses = mutableListOf<String>()
        if(!propertySpecification.fairnessON) {
            fairnessVariableStatuses.add("n.a.")
            return fairnessVariableStatuses
        }
        for(pId in cfgs.processes.indices) {
            if(this.contains(ff.literal("fr_${t}_${pId}", true))) {
                fairnessVariableStatuses.add("P$pId = fair")
            } else {
                fairnessVariableStatuses.add("P$pId = unfair")
            }
        }
        return fairnessVariableStatuses
    }

    /**
     * Using the SortedSet of literals it is called on, it derives from the truth values of the location literals, where each process is at timestep [t]
     * @param [t] timestep to find process locations for
     * @return list of strings denoting the timestep [t] location of each process
     */
    private fun SortedSet<Literal>.locationEvaluation(t: Int): MutableList<String> {
        val processLocations = mutableListOf<String>()
        for ((pId, process) in cfgs.processes.withIndex()) {
            var processLocation = ""
            for(d in 0 until digitRequired(process.numberOfLocations())) {
                processLocation += if(this.contains(ff.literal("n_${t}_${pId}_${d}", false))) {
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
        val bigAnd = mutableListOf<Formula>()
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
    
    private fun String.asFormula(t: Int): Formula {
        return p.parse(this.insertTimestamp(t))
    }

    /**
     * Replaces i in the string it is called on with [t] and I with ([t] + 1)
     *
     * @param t base timestep to insert into string
     * @return string with [t] inserted where placeholders were
     */
    private fun String.insertTimestamp(t: Int): String {
        return this.replace("i", "$t").replace("I", "${t + 1}")
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