package za.ac.up.tvamcus.runner

import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS

class Runner(private val cfgs: List<CFGS>, private val propertySpec: PropertySpecification) {
    fun evaluate() {
        if(propertySpec.multiModel) {
            val abstract = Evaluator(cfgs.last(), propertySpec)
            abstract.evaluate(startFrom = 0)
        }
        val concrete = Evaluator(cfgs.first(), propertySpec)
        concrete.evaluate(startFrom = 0)
    }
}