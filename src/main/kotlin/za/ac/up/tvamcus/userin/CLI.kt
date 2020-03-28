package za.ac.up.tvamcus.userin

import za.ac.up.tvamcus.evaluator.Evaluator
import za.ac.up.tvamcus.parser.Parser
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.runner.Runner
import za.ac.up.tvamcus.state.cfgs.CFGS
import java.text.ParseException

object CLI {
    @JvmStatic
    fun main(args: Array<String>) {
        try {
            val testPair = getTestPair()
            val runner = Runner(cfgs = testPair.first, propertySpec = testPair.second)
            runner.evaluate()
        } catch (e: Exception) {
            println(e.localizedMessage)
        }
    }

    private fun getTestPair(): Pair<MutableList<CFGS>, PropertySpecification> {
        val mm = multiModel()
        val cfgsList = allCFGS(mm)
        return Pair(
            cfgsList,
            PropertySpecification (
                multiModel = mm,
                processList = commaSeparatedProcessList().extractCSList(cfgsList.first()),
                type = type(),
                fairnessOn = fairnessOn(),
                operator = operator(cfgsList.first().processes.count()),
                location = location(),
                bound = getBound()
            )
        )
    }

    private fun getBound(): Int {
        do {
            print("Upper Bound: ")
            val bound = readLine()
            if(bound != null && bound.toInt() > 0) {
                println()
                return bound.toInt()
            } else {
                println("Bound has to be a non-negative integer.")
                print("Please try again - ")
            }
        } while (true)
    }

    private fun allCFGS(multiModel: Boolean): MutableList<CFGS> {
        val cfgs = mutableListOf<CFGS>()
        cfgs.add(getCFGS("File name (AllP) "))
        if(multiModel) {
            cfgs.add(getCFGS("File name (NoP) "))
        }
        return cfgs
    }

    private fun getCFGS(message: String): CFGS {
        while(true) {
            print(message)
            val file = readLine()
            if(file != null) {
                try {
                    val model = Parser().parseFile("/mnt/c/Users/josuabotha/Development/Tvamcus/inputFiles/$file.json")
                    println("...parsed")
                    return model
                } catch (e: ParseException) {
                    println("Model cannot be encoded.")
                    println("Please ensure that the json file follows the required specifications.")
                }
            } else {
                println("no file location specified")
            }
            println("...please try again")
        }
    }


    private fun type(): String{
        print("Liveness (l) or Reachability (r) ")
        val response = readLine()
        return if(response == null || response.decapitalize().first() == 'l') {
            "liveness"
        } else {
            "reachability"
        }
    }

    private fun location(): Int {
        while(true) {
            print("Target Location ")
            val response = readLine()
            if(response != null && response.toInt() >= 0) {
                return response.toInt()
            } else {
                println("Invalid Location, please enter an Integer location ID")
            }
        }
    }

    private fun commaSeparatedProcessList(): String {
        while(true) {
            print("Processes to Consider - as list (i.e. 0,7,3,2) or type 'a' for all ")
            val processCSList = readLine()
            if(processCSList != null) {
                return processCSList
            } else {
                println("You have to select something, ok")
            }
        }
    }

    private fun operator(processCount: Int): Char {
        if(processCount == 0) {
            return '&' // no processes, so any operator will do
        }
        while(true) {
            print("Operator (&/|): ")
            val operator = readLine()
            return if(operator != null && operator.first() == '&') {
                '&'
            } else {
                '|'
            }
        }
    }

    private fun fairnessOn(): Boolean {
        print("With Fairness? (y/n) ")
        val answer = readLine()
        return !(answer == null || answer.decapitalize().first() == 'n')
    }

    private fun multiModel(): Boolean {
        print("Multi Modal Approach? (y/n) ")
        val answer = readLine()
        return !(answer == null || answer.decapitalize().first() == 'n')
    }

    private fun String.extractCSList(model: CFGS): MutableList<Int> {
        var listTrimmed = this.dropLastWhile { it == ')' }.dropWhile { it == '(' }
        val list = mutableListOf<Int>()
        if (listTrimmed.decapitalize() == "all" || listTrimmed.decapitalize() == "a") {
            for (pId in model.processes.indices) {
                list.add(pId)
            }
        } else {
            while (listTrimmed.contains(',')) {
                list.add(listTrimmed.substringBefore(',').trim().toInt())
                listTrimmed = listTrimmed.substringAfter(',').trim()
            }
            list.add(listTrimmed.toInt())
            /*} else {
                throw IllegalArgumentException("List contains process ids that are not in the CFGS")
            }*/
        }
        return list
    }
}