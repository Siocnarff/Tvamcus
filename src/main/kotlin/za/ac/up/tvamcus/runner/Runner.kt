package za.ac.up.tvamcus.runner

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import za.ac.up.tvamcus.encoders.encLocation
import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.logbook.TimeLog
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.state.evaluation.State
import za.ac.up.tvamcus.userout.printSatisfiable
import java.lang.IllegalStateException
import kotlin.math.E

class Runner(private val cfgs: List<CFGS>, private val propertySpec: PropertySpecification) {

    fun evaluate(startFrom: Int = 0) {
        val timeLog = TimeLog()
        val concrete = Evaluator(cfgs.first(), propertySpec)
        if(propertySpec.multiModel) {
            val abstract = Evaluator(cfgs.last(), propertySpec)
            val aResult = abstract.evaluate(startFrom)
            if(aResult.first == Tristate.UNDEF) {
                val cResult =  concrete.evaluate(aResult.second.asFormula(), aResult.third, 0)
                cResult.second.print()
                printSatisfiable(timeLog.totalTime(), aResult.third)
            }
        } else {
            val cResult = concrete.evaluate(startFrom)
            cResult.second.print()
            printSatisfiable(timeLog.totalTime(), cResult.third)
        }
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

    /**
     * Experimental function
     */
    private fun MutableList<State>.asFormula(): MutableSet<Formula> {
        val bigAnd = mutableSetOf<Formula>()
        for(step in this) {
            for(location in step.locationStatus) {
                bigAnd.add(
                    parse(cfgs.first().encLocation(pId = location.first, lId = location.second, t = step.timestep))
                )
            }
        }
        return mutableSetOf(conjunct(bigAnd))
    }
}