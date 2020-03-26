package za.ac.up.tvamcus.parser

import za.ac.up.tvamcus.state.cfgs.*
import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import com.google.gson.stream.JsonReader
import com.google.gson.JsonElement
import com.google.gson.reflect.TypeToken
import java.io.File

object Parser {
    private var predicates: MutableMap<String, Int> = mutableMapOf()
    private var init: MutableMap<String, Boolean> = mutableMapOf()
    private val processes: MutableList<Process> = mutableListOf()

    private fun standardize(guard: String?): String {
        if (guard == null) {
            return "${'$'}true"
        }
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

    fun parseFile (filePath: String): CFGS {
        val builder = GsonBuilder()
        val g = builder.create()
        val fileBuffer = File(filePath).bufferedReader()
        val jsonReader = JsonReader(fileBuffer)
        val parser = JsonParser()
        val rootNode: JsonElement = parser.parse(jsonReader)
        val predicatesJson: JsonElement = rootNode.asJsonObject.get("predicates")
        val initJson: JsonElement = rootNode.asJsonObject.get("init")
        val processesJson: JsonElement = rootNode.asJsonObject.get("processes")
        val typeA = object : TypeToken<MutableMap<String, Int>>() {}.type
        val typeB = object : TypeToken<MutableMap<String, Boolean>>() {}.type
        predicates = g.fromJson(predicatesJson, typeA)
        init = g.fromJson(initJson, typeB)
        for ((idCounter, process) in processesJson.asJsonArray.withIndex()) {
            processes.add(
                Process(
                    id = idCounter,
                    transitions = mutableListOf()
                )
            )
            for (node in process.asJsonObject.get("states").asJsonArray) {
                for (transition in node.asJsonObject.get("transitions").asJsonArray) {
                    processes[idCounter].transitions.add(
                        g.fromJson(transition, CfgsTransition::class.java)
                    )
                    processes[idCounter].transitions.last().guard =
                        standardize(
                            processes[idCounter].transitions.last().guard
                        )
                    processes[idCounter].transitions.last().assignments.forEach {
                        it.RHS = standardize(it.RHS)
                    }
                }
            }
        }
        return CFGS(predicates, init, processes)
    }
}
