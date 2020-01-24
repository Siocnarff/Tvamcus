package za.ac.up

import za.ac.up.extensions.Encoder
import za.ac.up.extensions.Parser
import java.text.ParseException

//Note: jar build in Tvamcus/build/libs
//In windows run jar with "java -d64 -Xms50m -Xmx10g -jar Tvamcus-1.0.jar" for better performance
//however this is not fully optimized, and further JVM settings can be tested to attempt improvment

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

            val encoder = getEncoder()
            val test = getTest()
            val ev = encoder.Evaluator(test)
            ev.evaluate(getBound())

        } catch (e: Exception) {

            println(e.localizedMessage)

        }
    }

    private fun getEncoder(): Encoder {
        do {
            print("Input file name: ")
            val file = readLine()
            println()
            if(file != null) {
                try {
                    val model = Parser.parseFile("/C:/Code/Tuks/Development/Tvamcus/inputFiles/$file.json")
                    println("...parsed")
                    try {
                        return Encoder(model)
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

    private fun getTest(): Encoder.Test {
        print("\nLiveness or Reachability? (L/R): ")
        val type = readLine()
        if(type?.decapitalize() == "l" || type?.decapitalize() ==  "liveness") {
            do {
                print("Progress Location: ")
                val pLoc = readLine()
                if(pLoc != null && pLoc.toInt() >= 0) {
                    print("Processes to Consider - as list (i.e. 0,7,3,2) or type 'a/A' for all: ")
                    val processList = readLine()
                    if(processList != null) {
                        print("Operator (&/|): ")
                        val operator = readLine()
                        if(operator != null && (operator == "|" || operator == "&")) {
                            return Encoder.Test("liveness", pLoc.toInt(), processList, operator)
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
        } else {
            do {
                print("Error Location: ")
                val eLoc = readLine()
                if(eLoc != null && eLoc.toInt() >= 0) {
                    print("Processes to Consider - as list (i.e. 0,7,3,2) or type 'a/A' for all: ")
                    val processList = readLine()
                    if(processList != null) {
                        print("Operator (&/|): ")
                        val operator = readLine()
                        if (operator != null && (operator == "|" || operator == "&")) {
                            return Encoder.Test("reachability", eLoc.toInt(), processList, operator)
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
}