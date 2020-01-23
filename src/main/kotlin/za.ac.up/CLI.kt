package za.ac.up

import za.ac.up.extensions.Encoder
import za.ac.up.extensions.Parser
import java.io.FileWriter
import java.text.ParseException
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

object CLI {
    @JvmStatic
    fun main(args: Array<String>) {
        /*
        val current = LocalDateTime.now()
        val formatter = DateTimeFormatter.BASIC_ISO_DATE
        val dateTime = current.format(formatter)
        val startTime = System.nanoTime()
        */
        val encoder = getEncoderFromUser()
        val params = getParametersFromUser()
        try {
            encoder.Evaluator().evaluate(params)
        } catch (e: Exception) {
            println(e.localizedMessage)
        }
    }

    private fun getEncoderFromUser(): Encoder {
        do {
            print("Input file name: ")
            val file = readLine()
            println()
            if(file != null) {
                try {
                    val model = Parser.parseFile("/C:/Code/Tuks/Development/Tvamcus/inputFiles/$file.json")
                    println("...parsed")
                    try {
                        return Encoder(model, "reachability")
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

    private fun getParametersFromUser(): Encoder.Conditions {
        do {
            print("Error Location (Int): ")
            val eLocation = readLine()
            if(eLocation != null && eLocation.toInt() >= 0) {
                print("Upper Bound (Int): ")
                val bound = readLine()
                if(bound != null && bound.toInt() >= 0) {
                    println()
                    return Encoder.Conditions(eLocation.toInt(), bound.toInt())
                }
            }
        } while (true)
    }
}