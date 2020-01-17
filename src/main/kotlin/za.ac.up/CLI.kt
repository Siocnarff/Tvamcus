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
        // run program, and then input the file name etc from command line
        // place all files you want to parse in satBMC/inputFiles
        // please fix the path for files below so that it matches to your system

        // file that saves program run time
        val current = LocalDateTime.now()
        val formatter = DateTimeFormatter.BASIC_ISO_DATE
        val dateTime = current.format(formatter)
        //simply adding time to give file a unique name
        val file = FileWriter("/C:/Code/IdeaProjects/againTVMC/output/date${dateTime}_id${System.currentTimeMillis()}.txt")

        val encoder = getEncoderFromUser()
        val params = getParametersFromUser()
        val startTime = System.nanoTime()
        try {
            file.appendln(
                if (encoder.evaluate(params.eLocation, params.bound)) {
                    "error found"
                } else {
                    "no error found"
                }
            )
        } catch (e: Exception) {
            println(e.localizedMessage)
        }
        file.write("Program ran for: ")
        file.write(((startTime - System.nanoTime())/1000000000).toString())
        file.write(" seconds")
        file.close()
    }

    private data class Conditions(val eLocation: Int, val bound: Int)

    private fun getEncoderFromUser(): Encoder {
        do {
            print("Input file name: ")
            val file = readLine()
            println()
            if(file != null) {
                try {
                    val model = Parser.parseFile("/C:/Code/IdeaProjects/againTVMC/inputFiles/$file.json")
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

    private fun getParametersFromUser(): Conditions {
        do {
            print("Error Location (Int): ")
            val eLocation = readLine()
            if(eLocation != null && eLocation.toInt() >= 0) {
                print("Upper Bound (Int): ")
                val bound = readLine()
                if(bound != null && bound.toInt() >= 0) {
                    println()
                    return Conditions(eLocation.toInt(), bound.toInt())
                }
            }
        } while (true)
    }
}