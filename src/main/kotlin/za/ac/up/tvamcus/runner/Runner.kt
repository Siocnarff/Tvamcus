package za.ac.up.tvamcus.runner

import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.userin.CLI

object Runner {
    @JvmStatic
    fun main(args: Array<String>) {
        try {
            val testPair = CLI.getTestPair()
            val ev = Evaluator(controlFlowGraphState = testPair.first.first(), propertySpecification = testPair.second)
            ev.evaluateUniModel(CLI.getBound())
        } catch (e: Exception) {
            println(e.localizedMessage)
        }
    }
    fun evaluate(cfgs: List<CFGS>, propertySpec: PropertySpecification) {
        if(propertySpec.multiModel) {
            val abstract = Evaluator(cfgs.last(), propertySpec)
            abstract.evaluateUniModel(propertySpec.bound)
        }
        val concrete = Evaluator(cfgs.first(), propertySpec)
        concrete.evaluateUniModel(propertySpec.bound)
    }
}