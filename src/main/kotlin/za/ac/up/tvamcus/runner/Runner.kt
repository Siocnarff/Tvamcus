package za.ac.up.tvamcus.runner

import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS

class Runner(private val cfgs: List<CFGS>, private val propertySpec: PropertySpecification) {
    fun evaluate() {
        if(!propertySpec.multiModel) {
            Evaluator(propertySpec, cfgs.first())
        } else {
            val abstract = Evaluator(propertySpec, cfgs.last())
            val concrete = Evaluator(propertySpec, cfgs.last())
        }
    }
}