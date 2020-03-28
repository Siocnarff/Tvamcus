package za.ac.up.tvamcus.runner

import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS

class Runner(private val cfgs: List<CFGS>, private val propertySpec: PropertySpecification) {
    fun evaluate() {
        val concrete = Evaluator(cfgs.first(), propertySpec)
        if(!propertySpec.multiModel) {
        } else {
            val abstract = Evaluator(cfgs.last(), propertySpec)
        }
    }
}