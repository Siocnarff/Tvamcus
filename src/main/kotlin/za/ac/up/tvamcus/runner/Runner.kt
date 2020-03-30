package za.ac.up.tvamcus.runner

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import za.ac.up.tvamcus.encoders.encLocation
import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.logicng.conjunct
import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.state.evaluation.State
import java.lang.IllegalStateException
import kotlin.math.E

class Runner(private val cfgs: List<CFGS>, private val propertySpec: PropertySpecification) {

    fun evaluate(startFrom: Int = 0) {
        if(propertySpec.multiModel) {
            Evaluator(cfgs.last(), propertySpec).evaluate(startFrom).second.print()
        }
        Evaluator(cfgs.first(), propertySpec).evaluate(startFrom).second.print()
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
    private fun MutableList<State>.asFormula(): Formula { // TODO: Get Proper pId
        val bigAnd = mutableSetOf<Formula>()
        for((t, step) in this.withIndex()) {
            for(location in step.locationStatus) {
                bigAnd.add(
                    parse(cfgs.first().encLocation(pId = 0, lId = location.toInt(), t = t.toString()))
                )
            }
        }
        return conjunct(bigAnd)
    }
}