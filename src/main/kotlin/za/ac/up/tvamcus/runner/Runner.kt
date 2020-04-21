package za.ac.up.tvamcus.runner

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import za.ac.up.tvamcus.encoders.encLocation
import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.logbook.TimeLog
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.property.Configuration
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.state.evaluation.State
import za.ac.up.tvamcus.userout.printSatisfiable

class Runner(private val cfgs: List<CFGS>, private val config: Configuration) {

    private val concrete = Evaluator(cfgs.first(), config)
    private val abstract = Evaluator(cfgs.last(), config)

    fun evaluate(startFrom: Int = 0) {
        val timeLog = TimeLog()
        val result = if (config.multiModel) {
            evaluateMultiModel(startFrom)
        } else {
            evaluateUniModel(startFrom)
        }
        result.second.print()
        printSatisfiable(timeLog.totalTime(), result.third)
    }

    private fun evaluateMultiModel(
        startFrom: Int = 0,
        pc: Formula = parse("${'$'}true")
    ): Triple<Tristate, MutableList<State>, Int> {
        val aResult = abstract.evaluate(startFrom, pc)
        return if (aResult.first == Tristate.UNDEF) {
            val cResult = concrete.evaluate(aResult.second.asFormula(), aResult.third, startFrom)
            if (cResult.first == Tristate.TRUE) {
                cResult
            } else {
                evaluateMultiModel(cResult.third, conjunct(aResult.second.asFormula()).negate())
            }
        } else {
            aResult
        }
    }

    private fun evaluateUniModel(startFrom: Int): Triple<Tristate, MutableList<State>, Int> {
        return concrete.evaluate(startFrom)
    }


    private fun MutableList<State>.print() {
        this.forEachIndexed { index, stepStat ->
            println("\n$index:")
            println(stepStat.locationStatuses)
            println(stepStat.predicateStatus)
            println(stepStat.fairnessStatus)
            println(stepStat.reRdStatus)
        }
    }

    /**
     * Experimental function
     */
    private fun MutableList<State>.asFormula(): MutableSet<Formula> {
        val bigAnd = mutableSetOf<Formula>()
        this.forEach { step ->
            step.locationStatuses.mapTo(bigAnd) {
                parse(
                    cfgs.first().encLocation(pId = it.first, lId = it.second, t = step.timestep)
                )
            }
        }
        return mutableSetOf(conjunct(bigAnd))
    }
}