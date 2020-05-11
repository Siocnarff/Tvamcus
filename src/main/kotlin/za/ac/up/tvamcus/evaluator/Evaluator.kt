package za.ac.up.tvamcus.evaluator

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.Literal
import za.ac.up.tvamcus.encoders.digitRequired
import za.ac.up.tvamcus.encoders.encLocation
import za.ac.up.tvamcus.feedback.EvaluatorFeedback
import za.ac.up.tvamcus.logicng.LogicNG
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.property.Configuration
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.state.evaluation.State
import za.ac.up.tvamcus.taskbuilder.MCTaskBuilder
import za.ac.up.tvamcus.userout.printState
import java.util.*
import javax.naming.InsufficientResourcesException
import kotlin.math.pow

class Evaluator(private val cfgs: CFGS, private val config: Configuration) {
    private var runCount: Int = 0
    private val taskBuilder: MCTaskBuilder = MCTaskBuilder(this.cfgs, this.config)
    private val run: MutableSet<Formula> = mutableSetOf() // set of timestep encoded transition formulas

    /**
     * SAT-based k-bounded model checking runs from k = 0 to [config].bound +1
     */
    fun evaluate(startFrom: Int = 0, pc: Formula = parse("${'$'}true")): EvaluatorFeedback {
        if (runCount != startFrom) {
            println("R: ${run.size}, S: $startFrom")
            throw InsufficientResourcesException(
                "Cannot start from a timestep not yet reached in Evaluator.run"
            )
        }
        //val timeLog = TimeLog()
        run.add(pc)
        if (startFrom == 0) {
            run.add(taskBuilder.init)
        }
        for (t in startFrom..config.bound) {
            val property = taskBuilder.propertyFormula(t)
            val result = run.evaluateConjunctedWith(property, literal = "unknown")
            if (result == Tristate.TRUE) {
                val witness = resultPathInfo(t)
                //path.print()
                return if (run.evaluateConjunctedWith(property, literal = "~unknown") == Tristate.TRUE) {
                    //printSatisfiable(timeLog.totalTime(), t)
                    EvaluatorFeedback(Tristate.TRUE, witness, t)
                } else {
                    //printUnknown(timeLog.totalTime(), t)
                    EvaluatorFeedback(Tristate.UNDEF, witness, t)
                }
            }
            run.add(taskBuilder.cfgAsFormula(t))
            runCount++
        }
        return EvaluatorFeedback(Tristate.FALSE, mutableListOf(), config.bound)
        //printNoErrorFound(timeLog.totalTime(), propertySpec.bound)
    }

    fun evaluate(
        constraint: MutableSet<Formula>,
        k: Int,
        startFrom: Int = 0
    ): EvaluatorFeedback {
        println("......................Begin Again")
        //val timeLog = TimeLog()
        if (startFrom == 0) {
            run.add(taskBuilder.init)
        }
        for (t in startFrom..k) {
            run.add(taskBuilder.cfgAsFormula(t))
            runCount++
        }
        val property = conjunct(conjunct(constraint), taskBuilder.propertyFormula(k))
        if (run.evaluateConjunctedWith(property, literal = "unknown") == Tristate.TRUE) {
            val path = resultPathInfo(k)
            val result = run.evaluateConjunctedWith(property, literal = "~unknown")
            if (result == Tristate.UNDEF) {
                throw IllegalArgumentException("Not supposed to have unknown here, ensure CFGS contains ALL predicates")
            } else if (result == Tristate.TRUE) {
                return EvaluatorFeedback(Tristate.TRUE, path, k)
            }
        } else {
            println("Witness: $property")
            println("UnsatCore: ${LogicNG.solver.unsatCore()}")
        }
        return EvaluatorFeedback(Tristate.FALSE, mutableListOf(), k)
    }

    private fun MutableSet<Formula>.evaluateConjunctedWith(
        witness: Formula,
        literal: String
    ): Tristate {
        val startTime = System.nanoTime()
        LogicNG.solver.reset()
        LogicNG.solver.add(conjunct(conjunct(this), witness, parse(literal)))
        val result = LogicNG.solver.sat()
        val endTime = System.nanoTime()
        printState(endTime - startTime, result.toString())
        return result
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
            if (this.contains(LogicNG.ff.literal("re_$timestep", true))) "re = true" else "re = false",
            if (this.contains(LogicNG.ff.literal("rd_$timestep", true))) "rd = true" else "rd = false"
        )
    }

    /**
     * For the [timestep] timestep encoding of each predicate in the [cfgs], ascertain the truth value of said
     * predicate in the SortedSet of literals it is called on (this Set should be derived from the SAT model)
     *
     * @param [timestep] timestep to check predicate truth values
     * @return list of predicates and their respective truth values
     */
    private fun SortedSet<Literal>.predicateEvaluation(timestep: Int): MutableList<String> {
        val predicateStatuses = mutableListOf<String>()
        cfgs.predicates.forEach { p ->
            when {
                this.contains(LogicNG.ff.literal("${p.value}_${timestep}_u", true)) -> {
                    predicateStatuses.add("${p.key} = unknown")
                }
                this.contains(LogicNG.ff.literal("${p.value}_${timestep}_t", true)) -> {
                    predicateStatuses.add("${p.key} = true")
                }
                else -> {
                    predicateStatuses.add("${p.key} = false")
                }
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
        if (!config.fairnessOn) {
            fairnessVariableStatuses.add("n.a.")
            return fairnessVariableStatuses
        }
        for (pId in cfgs.processes.indices) {
            if (this.contains(LogicNG.ff.literal("fr_${timestep}_${pId}", true))) {
                fairnessVariableStatuses.add("P$pId = fair")
            } else {
                fairnessVariableStatuses.add("P$pId = unfair")
            }
        }
        return fairnessVariableStatuses
    }

    /**
     * Using the SortedSet of literals it is called on, it derives from the truth values
     * of the location literals, where each process is at timestep [timestep]
     * @param [timestep] timestep to find process locations for
     * @return list of strings denoting the timestep [timestep] location of each process
     */
    private fun SortedSet<Literal>.locationEvaluation(timestep: Int): MutableList<Pair<Int, Int>> {
        val processLocations = mutableListOf<Pair<Int, Int>>()
        for (process in cfgs.processes) {
            var processLocation = ""
            for (d in 0 until digitRequired(process.numberOfLocations())) {
                processLocation += if (
                    this.contains(LogicNG.ff.literal("n_${timestep}_${process.id}_${d}", false))
                ) {
                    "0"
                } else {
                    "1"
                }
            }
            processLocations.add(Pair(process.id, processLocation.toInt()))
        }
        return processLocations
    }

    private fun String.toInt(): Int {
        var tally = 0
        for ((index, c) in this.reversed().withIndex()) {
            tally += when (c) {
                '1' -> (2.0.pow(index)).toInt()
                '0' -> 0
                else -> throw error("String contains invalid characters, only 1, or 0 allowed.")
            }
        }
        return tally
    }

    private fun resultPathInfo(t: Int): MutableList<State> {
        return evaluationResultLiterals().pathInfo(t)
    }

    private fun evaluationResultLiterals(): SortedSet<Literal> {
        return LogicNG.solver.model().literals()
    }

    private fun SortedSet<Literal>.pathInfo(bound: Int): MutableList<State> {
        val steps = mutableListOf<State>()
        for (k in 0 until bound + 1) {
            steps.add(
                State(
                    k.toString(),
                    this.locationEvaluation(k),
                    this.predicateEvaluation(k),
                    this.fairnessEvaluation(k),
                    this.reRdEvaluation(k)
                )
            )

        }
        return steps
    }
}