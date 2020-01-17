package extensions

import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import com.google.gson.stream.JsonReader
import com.google.gson.JsonElement
import com.google.gson.JsonSyntaxException
import com.google.gson.reflect.TypeToken
import java.io.EOFException
import java.io.File
import java.io.FileNotFoundException

object Parser {
    data class Model (val predicates: Map<String, Int>, val processes: List<Process>)

    private var predicates: MutableMap<String, Int> = mutableMapOf()
    private val processes: MutableList<Process> = mutableListOf()

    data class Process (
        val id: Int,
        val transitions: MutableList<Transition>
    )

    data class Transition (
        val source: Int,
        val destination: Int,
        val assignments: List<Assignment>,
        var guard: String
    )

    data class Assignment (
        var RHS: String,
        val predicate: Int
    )

    val jsonStructureExample: String = """
            NOTE
            The file Json should conform to the following structure:

            {
              "predicates": {
                "(a = -1)": 0
              },
              "processes": [
                {
                  "states": [
                    {
                      "transitions": [
                        {
                          "source": 2,
                          "destination": 3,
                          "assignments": [
                            {
                              "RHS": "choice(false, true)",
                              "predicate": 0
                            }
                          ],
                          "guard": "choice((a = -1), (not (a = -1)))"
                        }
                      ]
                    }
                  ]
                }
              ]
            }      
        """.trimIndent()
    private fun exceptionMessages ( message: String, localizedMessage: String ) {
        println(message)
        println(localizedMessage.drop(localizedMessage.indexOf(':') + 2))
        println('\n' + jsonStructureExample)
    }

    private fun standardize(guard: String?): String {
        if (guard == null) {
            return "${'$'}true"
        } // else
        var standardGuard = ""
        var tempNot = ""
        var tempOr = ""
        var tempAnd = ""
        var tempTrue = ""
        var tempFalse = ""
        var temp = ""

        for(c in guard) {
            if(tempOr == "or") {
                standardGuard += temp.dropLast(2)
                temp = ""
                standardGuard += "|"
            }
            if (tempAnd == "and") {
                standardGuard += temp.dropLast(3)
                temp = ""
                standardGuard += "&"
            }
            if (tempNot == "not ") {
                standardGuard += temp.dropLast(4)
                temp = ""
                standardGuard += "~"
            }
            if (tempTrue == "true") {
                standardGuard += temp.dropLast(4)
                temp = ""
                standardGuard += "${'$'}true"
            }
            if (tempFalse == "false") {
                standardGuard += temp.dropLast(5)
                temp = ""
                standardGuard += "${'$'}false"
            }
            temp += c
            when(c) {
                'n' -> {
                    tempNot = ""
                }
                'o' -> {
                    tempOr = ""
                }
                'a' -> {
                    tempAnd = ""
                }
                't' -> {
                    tempTrue = ""
                }
                'f' -> {
                    tempFalse = ""
                }
                '(' -> {
                    standardGuard += temp.dropLast(1)
                    temp = "("
                }
                ')' -> {
                    standardGuard += if(predicates.containsKey(temp)) {
                        "${predicates[temp]}"
                    } else {
                        temp
                    }
                    temp = ""
                }
            }
            tempOr += c
            tempAnd += c
            tempNot += c
            tempTrue += c
            tempFalse += c
        }
        standardGuard += temp
        return standardGuard
    }

    fun parseFile (filePath: String): Model {
        val builder = GsonBuilder()
        val gson = builder.create()
        val fileBuffer = File(filePath).bufferedReader()
        val jsonReader = JsonReader(fileBuffer)
        val parser = JsonParser()
        val rootNode: JsonElement = parser.parse(jsonReader)
        val predicatesJson: JsonElement = rootNode.asJsonObject.get("predicates")
        val processesJson: JsonElement = rootNode.asJsonObject.get("processes")
        val type = object : TypeToken<MutableMap<String, Int>>() {}.type
        predicates = gson.fromJson(predicatesJson, type)
        for ((idCounter, process) in processesJson.asJsonArray.withIndex()) {
            processes.add(Process(id = idCounter, transitions = mutableListOf()))
            for (node in process.asJsonObject.get("states").asJsonArray) {
                for (transition in node.asJsonObject.get("transitions").asJsonArray) {
                    processes[idCounter].transitions.add(
                        gson.fromJson(transition, Transition::class.java)
                    )
                    processes[idCounter].transitions.last().guard = standardize(
                        processes[idCounter].transitions.last().guard
                    )
                    processes[idCounter].transitions.last().assignments.forEach {
                        it.RHS = it.RHS.replace("true", "${'$'}true").replace("false", "${'$'}false")
                    }
                }
            }
        }
        return Model(predicates, processes)
    }
}
