package za.ac.up.tvamcus.evaluator

import za.ac.up.tvamcus.logicng.LogicNG
import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.Literal
import za.ac.up.tvamcus.taskbuilder.MCTaskBuilder
import za.ac.up.tvamcus.encoders.*
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.userout.printState
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.*
import za.ac.up.tvamcus.state.evaluation.State
import java.lang.IllegalArgumentException
import java.util.*
import javax.naming.InsufficientResourcesException
import kotlin.math.pow

class Evaluator(controlFlowGraphState: CFGS, propertySpecification: PropertySpecification) {
    private val cfgs: CFGS = controlFlowGraphState
    private val propertySpec: PropertySpecification = propertySpecification
    private val taskBuilder: MCTaskBuilder = MCTaskBuilder(cfgs, propertySpec)
    private val run: MutableSet<Formula> = mutableSetOf() // set of timestep encoded transition formulas

    /**
     * SAT-based k-bounded model checking runs from k = 0 to [propertySpec].bound +1
     */
    fun evaluate(startFrom: Int = 0, pc: Formula = parse("${'$'}true")): Triple<Tristate, MutableList<State>, Int> {
        if(run.size != startFrom) {
            throw InsufficientResourcesException(
                "Cannot start from a timestep not yet reached in Evaluator.transitionsOverTime"
            )
        }
        //val timeLog = TimeLog()
        run.add(pc)
        if(startFrom == 0) {
            run.add(taskBuilder.init)
        }
        for (t in startFrom..propertySpec.bound) {
            val property = taskBuilder.propertyFormula(t)
            if (run.evaluateConjunctedWith(property, literal = "unknown") == Tristate.TRUE) {
                val path = resultPathInfo(t)
                //path.print()
                return if (run.evaluateConjunctedWith(property, literal = "~unknown") == Tristate.TRUE) {
                    //printSatisfiable(timeLog.totalTime(), t)
                    Triple(Tristate.TRUE, path, t)
                } else {
                    //printUnknown(timeLog.totalTime(), t)
                    Triple(Tristate.UNDEF, path, t)
                }
            }
            run.add(taskBuilder.cfgAsFormula(t))
        }
        return Triple(Tristate.FALSE, mutableListOf(), propertySpec.bound)
        //printNoErrorFound(timeLog.totalTime(), propertySpec.bound)
    }

    fun evaluate(constraint: MutableSet<Formula>, k: Int, startFrom: Int = 0): Pair<Tristate, MutableList<State>> {
        println("Begin Again")
        //val timeLog = TimeLog()
        for (t in startFrom..k) {
            run.add(taskBuilder.cfgAsFormula(t))
        }
        val property = taskBuilder.propertyFormula(k)
        if (run.evaluateConjunctedWith(property, constraint, literal = "unknown") == Tristate.TRUE) {
            val path = resultPathInfo(k)
            val result = run.evaluateConjunctedWith(property, constraint, literal = "~unknown")
            if (result == Tristate.UNDEF) {
                throw IllegalArgumentException("Not supposed to have unknown here, ensure CFGS contains ALL predicates")
            } else if(result == Tristate.TRUE) {
                return Pair(Tristate.TRUE, path)
            }
        }
        return Pair(Tristate.FALSE, mutableListOf())
    }

    private fun MutableSet<Formula>.evaluateConjunctedWith(
        property: Formula,
        constraint: MutableSet<Formula> = mutableSetOf(),
        literal: String
    ): Tristate {
        val startTime = System.nanoTime()
        LogicNG.solver.reset()
        if(constraint.isNotEmpty()) {
            LogicNG.solver.add(conjunct(conjunct(this), property, parse(literal), conjunct(constraint)))
        } else {
            LogicNG.solver.add(conjunct(conjunct(this), property, parse(literal)))
        }
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
        for(p in cfgs.predicates) {
            if(this.contains(LogicNG.ff.literal("${p.value}_${timestep}_u", true))) {
                predicateStatuses.add("${p.key} = unknown")
            } else if(this.contains(LogicNG.ff.literal("${p.value}_${timestep}_t", true))) {
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
        if(!propertySpec.fairnessOn) {
            fairnessVariableStatuses.add("n.a.")
            return fairnessVariableStatuses
        }
        for(pId in cfgs.processes.indices) {
            if(this.contains(LogicNG.ff.literal("fr_${timestep}_${pId}", true))) {
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
            for(d in 0 until digitRequired(process.numberOfLocations())) {
                processLocation += if(
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

    private fun SortedSet<Literal>.pathInfo(bound: Int): MutableList<State> {
        val steps = mutableListOf<State>()
        for(k in 0 until bound + 1) {
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

    private fun resultPathInfo(t: Int): MutableList<State> {
        return evaluationResultLiterals().pathInfo(t)
    }

    private fun evaluationResultLiterals(): SortedSet<Literal> {
        return LogicNG.solver.model().literals()
    }
}

/*fun modelCheckNoOpt(bound: Int) {
        val stepResults = mutableListOf<Tristate>()
        val timestepCfgsFormulas = mutableListOf<Formula>()
        val timeLog = TimeLog()

        timestepCfgsFormulas.add(taskBuilder.initialState)
        for (t in 0 until bound + 1) {
            val propertyFormula = taskBuilder.propertyFormula(t)
            print(" k(a)=$t")
            timeLog.startLap()
            stepResults.add(
                timestepCfgsFormulas.evaluateConjunctedWith(property = propertyFormula, literal = "unknown")
            )
            timeLog.endLap()
            printState(timeLog.lastLapTime(), stepResults.last().toString())
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = resultPathInfo(t)
                print(" k(b)=$t")
                timeLog.startLap()
                stepResults.add(
                    timestepCfgsFormulas.evaluateConjunctedWith(property = propertyFormula, literal = "~unknown")
                )
                timeLog.endLap()
                printState(timeLog.lastLapTime(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    println("\nError Path")
                    resultPathInfo(t).print()
                    printSatisfiable(timeLog.totalTime(), t)
                    if(propertySpec.doubleTest) {
                        timestepCfgsFormulas.last().solveAgainWithConstraint(
                            pathFormula(evaluationResultLiterals().pathInfo(t)), t, bound
                        )
                    }
                } else {
                    pathInfo.print()
                    printUnknown(timeLog.totalTime(), t)
                    if(propertySpec.doubleTest) {
                        timestepCfgsFormulas.last().solveAgainWithConstraint(pathFormula(pathInfo), t, bound)
                    }

                }
                return
            }
            timestepCfgsFormulas.add(conjunct(timestepCfgsFormulas.last(), taskBuilder.cfgAsFormula(t)))
        }
        timeLog.endLap()
        printNoErrorFound(timeLog.totalTime(), bound)
    }

    private fun Formula.solveAgainWithConstraint(constraint: Formula, startIndex: Int, bound: Int) {
        println("\n=============================================================================")
        println("============= Solving Again with constraint - restarting timer ==============")
        println("=============================================================================\n")
        val stepResults = mutableListOf<Tristate>()
        val timeLog = TimeLog()
        val formulas = mutableListOf<Formula>()
        formulas.add(conjunct(this, constraint))
        for (t in startIndex until bound + 1) {
            val propertyFormula = taskBuilder.propertyFormula(t)
            print(" k(a)=$t")
            timeLog.startLap()
            stepResults.add(
                formulas.evaluateConjunctedWith(property = propertyFormula, literal = "unknown")
            )
            timeLog.endLap()
            printState(timeLog.lastLapTime(), stepResults.last().toString())
            if (stepResults.last() == Tristate.TRUE) {
                val pathInfo = resultPathInfo(t)
                print(" k(b)=$t")
                timeLog.startLap()
                stepResults.add(
                    formulas.evaluateConjunctedWith(property = propertyFormula, literal = "~unknown")
                )
                timeLog.endLap()
                printState(timeLog.lastLapTime(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    println("\nError Path")
                    resultPathInfo(t).print()
                    printSatisfiable(timeLog.lastLapTime(), t)
                } else {
                    pathInfo.print()
                    printUnknown(timeLog.lastLapTime(), t)
                }
                return
            }
            formulas.add(conjunct(formulas.last(), taskBuilder.cfgAsFormula(timestep = t)))
        }
    }*/