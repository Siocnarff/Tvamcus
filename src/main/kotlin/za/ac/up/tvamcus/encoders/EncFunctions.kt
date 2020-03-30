package za.ac.up.tvamcus.encoders

import za.ac.up.tvamcus.logicng.parse
import za.ac.up.tvamcus.sets.ConjunctiveSet
import za.ac.up.tvamcus.sets.DisjunctiveSet
import za.ac.up.tvamcus.state.encoded.*
import za.ac.up.tvamcus.state.cfgs.*
import kotlin.math.ceil
import kotlin.math.log2
/**
 * Encodes all possible state space Transitions from i to I
 *
 * This encoding is in the form of  DisjunctiveSet<Transition>
 *
 * by Definition 11 in SCP19
 */
fun CFGS.encodeAsTemplateTransitionSet(): DisjunctiveSet<Transition> {
    val over: MutableSet<Transition> = mutableSetOf()
    for(process in processes) {
        for (transition in process.transitions) {
            over.add(
                this.encTransition(process.id, transition)
            )
        }
    }
    println("...CFGSEncoded")
    return DisjunctiveSet(over)
}

/**
 * Derives the full list of predicates in [CFGS] but now encoded
 */
fun CFGS.deriveEncodedPredicates(): Set<String> {
    val predicates: MutableSet<String> = mutableSetOf()
    for (p in this.predicates) {
        predicates.add("${p.value}_i_u")
        predicates.add("${p.value}_i_t")
    }
    for (process in this.processes) {
        for (d in 0 until digitRequired(process.numberOfLocations())) {
            predicates.add("n_i_${process.id}_${d}")
        }
    }
    return predicates
}

/**
 * Encodes a state space Transition from i to I
 *
 * by Definition 11 in SCP19
 *
 * @param pId the process to which the transition belongs
 * @param transition the [CFGS] transition being encoded
 * @return Encoded Transition belonging to [pId], from i to I
 */
fun CFGS.encTransition(pId: Int, transition: CfgsTransition): Transition {
    return Transition(
        pId,
        this.encLocation(pId, lId = transition.source, t =  "i"),
        encOperation(transition),
        this.encLocation(pId, lId = transition.destination, t = "I"),
        ConjunctiveSet(encIdleAllProcessesExcept(pId))
    )
}

/**
 * Encodes location
 *
 * by Definition 8 in SCP19
 *
 * @param pId ID of process the location belongs to
 * @param t the t location is encoded for, by default placeholder "i" is used
 * @return enc(loc)_i
 */
fun CFGS.encLocation(pId: Int, lId: Int, t: String = "i"): String {
    val digit = digitRequired(this.processes[pId].numberOfLocations())
    var output = ""
    var binaryId = toBinaryString(lId)
    while(binaryId.length < digit) {
        binaryId = "0$binaryId"
    }
    for((d, c) in binaryId.withIndex()) {
        val atom = "n_${t}_${pId}_${d}"
        output +=  if(c == '1') {
            "$atom & "
        } else {
            "~$atom & "
        }
    }
    return "(${output.dropLast(3)})"
}

/**
 * Encodes location as copy
 *
 * by Definition 8 in SCP19
 *
 * @param pId ID of process the location belongs to
 * @param t the t location is encoded for, by default placeholder "i" is used
 * @return enc(loc)_i_c
 */
fun CFGS.encLocationCopy(pId: Int, lId: Int, t: String = "i"): String {
    val digit = digitRequired(this.processes[pId].numberOfLocations())
    var output = ""
    var binaryId = toBinaryString(lId)
    while(binaryId.length < digit) {
        binaryId = "0$binaryId"
    }
    for((d, c) in binaryId.withIndex()) {
        val atomC = "n_${t}_${pId}_${d}_c"
        output +=  if(c == '1') {
            "$atomC & "
        } else {
            "~$atomC & "
        }
    }
    return "(${output.dropLast(3)})"
}

/**
 * Encodes that the operation associated with [transition] is executed form i to I
 *
 * by Definition 11 in SCP19
 *
 * @param transition the transition operation being encoded is derived from
 * @return the encoding of the execution of the operation
 */
private fun CFGS.encOperation(transition: CfgsTransition): Operation {
    val butChange = mutableSetOf<Int>()
    val bigAnd = mutableSetOf<String>()
    for(a in transition.assignments) {
        butChange.add(a.predicate)
        bigAnd.add(encAssignmentExpression(predicate = a.predicate, expression = a.RHS))
    }
    bigAnd.addAll(this.encUnchangingPredicateValues(butChange).conjunctOver)
    return Operation(
        guard = encGuard(transition.guard),
        assignments = ConjunctiveSet(bigAnd)
    )
}

/**
 * Encodes the guard it is called on
 *
 * by Definition 10 in SCP19
 *
 * @return encoded guard
 */
private fun encGuard(guard: String): String {
    return if (guard.startsWith("choice(")) {
        val choices = guard.drop(7).dropLast(1)
        encGuardChoice(
            choices.substringBefore(','),
            choices.substringAfter(',').dropWhile { it == ' ' }
        )
    } else {
        encExp("(${parse(guard).nnf()})")
    }
}

/**
 * Encodes a guard choice
 *
 * by Definition 10 in SCP19
 *
 * @param left the left hand option of a guard choice
 * @param right the right hand option of a guard choice
 * @return encoded guard
 */
private fun encGuardChoice(left: String, right: String): String {
    return if(left == "${'$'}true") {
        "${'$'}true"
    } else if(right == "${'$'}true") {
        "${'$'}false"
    } else if(left == "${'$'}false" && right == "${'$'}false") {
        "unknown"
    } else {
        "((${encExp(left)} | ${encExp(right, negate = true)}) & (${encExp(left)} | ${encExp(right)} | unknown))"
    }
}

/**
 * Encodes the assignment of [expression] to the predicate it is called on
 *
 * If [expression] is not a choice() turn it into one and call [encAssignmentChoice]
 * by Definition 11 in SCP19
 *
 * @param expression data on how to assign the predicate
 * @return encoded assignment
 */
private fun encAssignmentExpression(predicate: Int, expression: String): String {
    return if (expression.startsWith("choice(")) {
        encAssignmentChoice(
            predicate,
            expression.substring(7, expression.indexOf(',')),
            expression.dropLast(1).substring(expression.indexOf(',') + 2)
        )
    } else {
        encAssignmentChoice(predicate, expression, "~$expression")
    }
}

/**
 * Encodes that the values of all predicates, except [modifiedPredicates], remain unchanged from t i to I
 *
 * by Definition 11 in SCP19
 *
 * @param modifiedPredicates the predicates that are affected by the current assignment
 * @return Constraint that the non-modified predicates do not change from i to I
 */
private fun CFGS.encUnchangingPredicateValues(modifiedPredicates: MutableSet<Int>): ConjunctiveSet<String> {
    val bigAnd = mutableSetOf<String>()
    if(this.predicates.isEmpty()) {
        return ConjunctiveSet(bigAnd)
    }
    for(p in this.predicates) {
        if(!modifiedPredicates.contains(p.value)) {
            bigAnd.add(encAssignmentChoice(p.value, "${p.value}", "~${p.value}"))
        }
    }
    return ConjunctiveSet(bigAnd)
}

/**
 * Encodes predicate assignment, based on choice([left], [right])
 *
 * by Definition 11 in SCP19
 *
 * @param left left hand of choice
 * @param right right hand of choice
 * @param predicateId the predicate that the choice expression is assigned to
 */
private fun encAssignmentChoice(predicateId: Int, left: String, right: String): String {
    return if (left == "${'$'}true" && left == "${'$'}false") {
        encIsTrue(predicateId)
    } else if (left == "${'$'}false" && right == "${'$'}true") {
        encIsFalse(predicateId)
    } else if (right == "${'$'}false" && left == "${'$'}false") {
        encIsUnknown(predicateId)
    } else {
        "((${encExp(left)} & ${encIsTrue(predicateId)}) | (${encExp(right)} & ${encIsFalse(predicateId)}) | " +
        "(${encExp("($left | $right)", true).replace("unknown", "${'$'}true")}" +
        " & ${encIsUnknown(predicateId)}))"
    }
}

/**
 * Encodes that all processes except [activeProcess] make an idle step from i to I
 *
 * Encoded by the constraint that the locations of the idling processes do not change from i to I
 * by Definition 11 in SCP19
 *
 * @param activeProcess the process that executes when we move from t i to I
 * @return the encoding of the idling of non-active processes
 */
private fun CFGS.encIdleAllProcessesExcept(activeProcess: Int): MutableSet<String> {
    val conjunctOver = mutableSetOf<String>()
    for(p in this.processes) {
        if(activeProcess != p.id) {
            val tally = p.numberOfLocations()
            for(locationId in 0..tally) {
                for(d in 0..digitRequired(tally)) {
                    conjunctOver.add("(n_i_${p.id}_${d} <=> n_I_${p.id}_${d})")
                }
            }
        }
    }
    return conjunctOver
}

/**
 * Encodes the expression it is called on
 *
 * by Definition 10 in SCP19
 *
 * @param t the t the expression is encoded for (by default placeholder "i" is used)
 * @param negate if TRUE, expression is negated before being encoded
 * @return enc(exp)_i
 */
private fun encExp(expression: String, negate: Boolean = false, t: String = "i"): String {
    var output = ""
    var predicate = ""
    var operator = ""
    var previousWasPredicate = false

    val exp = if(negate) {
        "(${parse(expression).negate().nnf()})"
    } else {
        expression
    }

    for (c in exp) {
        if (c == ' ' || c == '&' || c == '|' || c == '(' || c == ')') {
            if (previousWasPredicate) {
                if (predicate != "") {
                    output += encPredicate(predicate, t)
                    predicate = ""
                }
                operator += c
                previousWasPredicate = false
            } else {
                operator += c
            }
        } else {
            if (!previousWasPredicate) {
                if (operator != "") {
                    output += operator
                    operator = ""
                }
                predicate += c
                previousWasPredicate = true
            } else {
                predicate += c
            }
        }
    }
    return if (output == "") {
        encPredicate(predicate, t)
    } else {
        output + operator
    }
}

/**
 * Creates the binary representation of an integer from a decimal input
 *
 * @return binary string of input integer
 */
fun toBinaryString(int: Int): String {
    return if(int / 2 > 0) {
        "${toBinaryString(int / 2)}${int % 2}"
    } else {
        "${int % 2}"
    }
}

/**
 * Calculates the number of bits required to name a given amount of nodes using binary
 *
 * @param numLocations the number of locations that have to be named
 * @return the amount of bits required
 */
fun digitRequired(numLocations: Int): Int {
    return if (numLocations == 1) {
        1
    } else {
        ceil(log2(numLocations.toDouble())).toInt()
    }
}

/**
 * Encodes the predicate (a string representation of an int) it is called on
 *
 * by Definition 10 in SCP19
 *
 * @param t predicate is encoded for (by default placeholder "i" is used)
 * @return enc(p)
 */
fun encPredicate(predicateId: String, t: String = "i"): String {
    if (predicateId == "") {
        return ""
    }
    return if (predicateId[0] == '~') {
        when (val p = predicateId.substring(1)) {
            "${'$'}true" -> "${'$'}false"
            "${'$'}false" -> "${'$'}true"
            else -> "((${p}_${t}_u & unknown) | (~${p}_${t}_u & ~${p}_${t}_t))"
        }
    } else {
        when (predicateId) {
            "${'$'}true" -> "${'$'}true"
            "${'$'}false" -> "${'$'}false"
            else -> "((${predicateId}_${t}_u & unknown) | (~${predicateId}_${t}_u & ${predicateId}_${t}_t))"
        }
    }
}

/**
 * Encodes that the predicate it is called on is unknown at the next t
 *
 * by Definition 9 in SCP19
 *
 * @param t predicate is unknown on (by default placeholder "I" is used)
 * @return enc(p = unknown)
 */
fun encIsUnknown(predicateId: Int, t: String = "I"): String {
    return "${predicateId}_${t}_u"
}

/**
 * Encodes a copy of the fact that the predicate it is called on is false at the next t
 *
 * by Definition 9 in SCP19
 *
 * @param t predicate is false on (by default placeholder "I" is used)
 * @return enc(p = false) copy
 */
fun encIsFalseCopy(predicateId: Int, t: String = "I"): String {
    return "(~${predicateId}_${t}_u_c & ~${predicateId}_${t}_t_c)"
}

/**
 * Encodes that the predicate it is called on is false at the next t
 *
 * by Definition 9 in SCP19

 *
 * @param t predicate is false on (by default placeholder "I" is used)
 * @return enc(p = false)
 */
fun encIsFalse(predicateId: Int, t: String = "I"): String {
    return "(~${predicateId}_${t}_u & ~${predicateId}_${t}_t)"
}

/**
 * Encodes a copy of the fact that the predicate it is called on is true at the next t
 *
 * by Definition 9 in SCP19
 *
 * @param t predicate is true on (by default placeholder "I" is used)
 * @return enc(p = true) copy
 */
fun encIsTrueCopy(predicateId: Int, t: String = "I"): String {
    return "(~${predicateId}_${t}_u_c & ${predicateId}_${t}_t_c)"
}

/**
 * Encodes that the predicate it is called on is true at the next t
 *
 * by Definition 9 in SCP19
 *
 * @param t predicate is true on (by default placeholder "I" is used)
 * @return enc(p = true)
 */
fun encIsTrue(predicateId: Int, t: String = "I"): String {
    return "(~${predicateId}_${t}_u & ${predicateId}_${t}_t)"
}

/*
package za.ac.up.tvamcus.view

import za.ac.up.tvamcus.parser.Parser
import za.ac.up.tvamcus.property.PropertySpecification
import za.ac.up.tvamcus.state.cfgs.CFGS
import za.ac.up.tvamcus.evaluator.Evaluator
import java.text.ParseException

object CLILegacy {
    @JvmStatic
    fun main(args: Array<String>) {
        try {
            val cfgs = getCFGS()
            val property = getPropertySpecificationOf(cfgs)
            val ev = Evaluator(property, cfgs)
            ev.evaluateUniModel(getBound())
        } catch (e: Exception) {

            println(e.localizedMessage)

        }
    }

    private fun getAllCFGS(multiModel: Boolean) {
        val cfgs = mutableListOf<CFGS>()
        println("All Predicates Version: ")
        cfgs.add(getCFGS())
        if(multiModel) {
            println("No Predicates Version:")
            cfgs.add(getCFGS())
        }
    }

    private fun getCFGS(): CFGS {
        do {
            print("Input file name: ")
            val file = readLine()
            println()
            if(file != null) {
                try {
                    val model = Parser.parseFile("/mnt/c/Users/josuabotha/Development/Tvamcus/inputFiles/$file.json")
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

    private fun getPropertySpecificationOf(model: CFGS): PropertySpecification {

        print("\nMulti Model Approach? (y/n): ")
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
                                    return PropertySpecification("liveness", pLoc.toInt(), processList, operator, fairnessOn, doubleTest)
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
                            return PropertySpecification("reachability", eLoc.toInt(), processList, operator, doubleTest)
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
        }
        return list
    }
}
 */
