package za.ac.up

import za.ac.up.extensions.Encoder
import za.ac.up.extensions.Parser
import java.text.ParseException

//Note: jar build in Tvamcus/build/libs
//In windows run jar with "java -d64 -Xms50m -Xmx10g -jar Tvamcus-1.0.jar" for better performance
//however this is not fully optimized, and further JVM settings can be tested to attempt improvement

object CLI {
    @JvmStatic
    fun main(args: Array<String>) {
        /*
        val current = LocalDateTime.now()
        val formatter = DateTimeFormatter.BASIC_ISO_DATE
        val dateTime = current.format(formatter)
        val startTime = System.nanoTime()
        */
        try {

            val model = getModel()
            val test = getPropertySpecificationOf(model)
            val encoder = Encoder(model)
            val ev = encoder.MCTaskBuilder(test)
            ev.evaluateNoOptimization(getBound())

        } catch (e: Exception) {

            println(e.localizedMessage)

        }
    }

    private fun getModel(): Parser.CFGS {
        do {
            print("Input file name: ")
            val file = readLine()
            println()
            if(file != null) {
                try {
                    val model = Parser.parseFile("/C:/Code/Tuks/Development/Tvamcus/inputFiles/$file.json")
                    println("...parsed")
                    try {
                        return model
                    } catch (e: ParseException) {
                        println("Model cannot be encoded.")
                        println("Please ensure that the json file follows the required specifications.")
                    }
                } catch (e: Exception) {
                    println(e.localizedMessage)
                }
            } else {
                println("no file location specified")
            }
            println("...please try again")
        } while (true)
    }

    private fun getPropertySpecificationOf(model: Parser.CFGS): Encoder.PropertySpecification {

        print("\nDouble Test? (y/n): ")
        val dt = readLine()
        val doubleTest = !(dt == null || dt.decapitalize().contains('n'))

        print("Liveness or Reachability? (l/r): ")
        val type = readLine()
        if(type?.decapitalize() == "l" || type?.decapitalize() ==  "liveness") {
            do {
                print("With Fairness? (y/n): ")
                val answer = readLine()
                if(answer != null) {
                    val fairnessOn = (answer.decapitalize() == "y")
                    do {
                        print("Progress Location: ")
                        val pLoc = readLine()
                        if(pLoc != null && pLoc.toInt() >= 0) {
                            print("Processes to Consider - as list (i.e. 0,7,3,2) or type 'a' for all: ")
                            val processCSList = readLine()
                            if(processCSList != null) {
                                val processList = if (processCSList.decapitalize().contains('a')) {
                                    model.processes.indices.toMutableList()
                                } else {
                                    processCSList.extractCSList(model)
                                }
                                val operator = if(processList.size != 1) {
                                    print("Operator (&/|): ")
                                    readLine()
                                } else {
                                    "&" // since only only one process in list, any operator will do, so user does not need to select one
                                }
                                if(operator != null && (operator == "|" || operator == "&")) {
                                    return Encoder.PropertySpecification("liveness", pLoc.toInt(), processList, operator, fairnessOn, doubleTest)
                                } else {
                                    println("Please try again, note '|' -> 'or' but '&' -> 'and'. Please type out the symbols themselves.")
                                }
                            } else {
                                print("Please try again - ")
                            }
                        } else {
                            println("Formula must be sound and in unparsed string format.")
                            print("Please try again - ")
                        }
                    } while(true)
                }
            } while (true)
        } else {
            do {
                print("Error Location: ")
                val eLoc = readLine()
                if(eLoc != null && eLoc.toInt() >= 0) {
                    print("Processes to Consider - as list (i.e. 0,7,3,2) or type 'a' for all: ")
                    val processCSList = readLine()
                    if(processCSList != null) {
                        val processList = if (processCSList.decapitalize().contains('a')) {
                            model.processes.indices.toMutableList()
                        } else {
                            processCSList.extractCSList(model)
                        }
                        val operator = if(processList.size != 1) {
                            print("Operator (&/|): ")
                            readLine()
                        } else {
                            "&" // since only only one process in list, any operator will do, so user does not need to select one
                        }
                        if (operator != null && (operator == "|" || operator == "&")) {
                            return Encoder.PropertySpecification("reachability", eLoc.toInt(), processList, operator, doubleTest = doubleTest)
                        } else {
                            println("Please try again, note:\n'|' -> 'or' but '&' -> 'and'. Please type out the symbols themselves.")
                        }
                    } else {
                        print("Please try again - ")
                    }
                } else {
                    println("Error Location has to be a non-negative integer.")
                    print("Please try again - ")
                }
            } while(true)
        }
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

    private fun String.extractCSList(model: Parser.CFGS): MutableList<Int> {
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
        }
        return list
    }
}