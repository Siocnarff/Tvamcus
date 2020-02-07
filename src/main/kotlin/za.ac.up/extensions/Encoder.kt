package za.ac.up.extensions

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.formulas.Literal
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import java.util.*
import kotlin.math.ceil
import kotlin.math.log2
import kotlin.math.pow

class Encoder(private val CFGS: Parser.CFGS) {

    data class ConjunctOver<T>(val conjunctOver: List<T>)

    data class DisjoinOver<T>(val disjoinOver: MutableList<T> = mutableListOf())

    /**
     * Information for evaluation of [timestepTemplate]
     *
     * @param type "liveness" or "reachability"
     * @param location progressLocationId if type is liveness, else errorLocationId
     * @param processList list of processes to be considered
     * @param operator (| or &) indicates if processList should be conjuncted or disjoined
     * @param fairnessON if TRUE then fairness should be checked
     */
    data class PropertySpecification(
        val type: String,
        val location: Int,
        val processList: List<Int>,
        val operator: String,
        val fairnessON: Boolean = false,
        val doubleTest: Boolean = false
    )

    /**
     * An encoded Control Flow Transition as an encoded guard and a list of encoded assignments
     *
     * @param guard encoded guard
     * @param assignments list of encoded assignments
     */
    data class Operation(val guard: String, val assignments: ConjunctOver<String>)

    /**
     * Two nodes and the transition between them, all encoded
     *
     * @param parentProcess id of process to whom this belongs
     * @param oldLocation location from which transition originated, encoded
     * @param operation the transition between the nodes, encoded
     * @param newLocation location to which transition goes, encoded
     * @param idle list created when [encIdleAllProcessesExcept] has been called on all processes save the [parentProcess]
     */
    data class Transition(
        val parentProcess: Int,
        val oldLocation: String,
        val operation: Operation,
        val newLocation: String,
        val idle: ConjunctOver<String>
    )

    /**
     * Encoded [CFGS] using three valued abstraction
     *
     * Contains general timestep indicators i and I (denoting i + 1) to be replaced upon formula creation with non-negative integers
     */
    private val timestepTemplate: DisjoinOver<Transition> = DisjoinOver()

    private data class State(
        val timestep: Int,
        val locationStatus: MutableList<String>,
        val predicateStatus: MutableList<String>,
        val fairnessStatus: MutableList<String>,
        val reRdStatus: Pair<String, String>
    )
    companion object {
        private val ff = FormulaFactory()
        private val p = PropositionalParser(ff)
        private val solver: MiniSat = MiniSat.glucose(ff)
    }
    init {
        encodeTransitions()
    }

    /**
     * Encodes location
     *
     * by Definition 7
     *
     * @param pId ID of process the location belongs to
     * @param timestep the timestep location is encoded for, by default placeholder "i" is used
     * @return enc(loc)_i
     */
    private fun Int.encLocation(pId: Int, timestep: String = "i"): String {
        val digit = digitRequired(CFGS.processes[pId].numberOfLocations())
        var output = ""
        var binaryId = this.toBinaryString()
        while(binaryId.length < digit) {
            binaryId = "0$binaryId"
        }
        for((d, c) in binaryId.withIndex()) {
            val atom = "n_${timestep}_${pId}_${d}"
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
     * by Definition 13
     *
     * @param pId ID of process the location belongs to
     * @param timestep the timestep location is encoded for, by default placeholder "i" is used
     * @return enc(loc)_i_c
     */
    private fun Int.encLocationCopy(pId: Int, timestep: String = "i"): String {
        val digit = digitRequired(CFGS.processes[pId].numberOfLocations())
        var output = ""
        var binaryId = this.toBinaryString()
        while(binaryId.length < digit) {
            binaryId = "0$binaryId"
        }
        for((d, c) in binaryId.withIndex()) {
            val atomC = "n_${timestep}_${pId}_${d}_c"
            output +=  if(c == '1') {
                "$atomC & "
            } else {
                "~$atomC & "
            }
        }
        return "(${output.dropLast(3)})"
    }

    /**
     * Creates the binary representation of an integer from a decimal input
     *
     * @return binary string of input integer
     */
    private fun Int.toBinaryString(): String {
        return if(this / 2 > 0) {
            "${(this / 2).toBinaryString()}${this % 2}"
        } else {
            "${this % 2}"
        }
    }

    /**
     * Encodes that the predicate it is called on is true at the next timestep
     *
     * by Definition 8
     *
     * @param timestep predicate is true on (by default placeholder "I" is used)
     * @return enc(p = true)
     */
    private fun String.encIsTrue(timestep: String = "I"): String {
        return "(~${this}_${timestep}_u & ${this}_${timestep}_t)"
    }

    /**
     * Encodes a copy of the fact that the predicate it is called on is true at the next timestep
     *
     * by Definition 8
     *
     * @param timestep predicate is true on (by default placeholder "I" is used)
     * @return enc(p = true) copy
     */
    private fun String.encIsTrueCopy(timestep: String = "I"): String {
        return "(~${this}_${timestep}_u_c & ${this}_${timestep}_t_c)"
    }

    /**
     * Encodes that the predicate it is called on is false at the next timestep
     *
     * by Definition 8
     *
     * @param timestep predicate is false on (by default placeholder "I" is used)
     * @return enc(p = false)
     */
    private fun String.encIsFalse(timestep: String = "I"): String {
        return "(~${this}_${timestep}_u & ~${this}_${timestep}_t)"
    }

    /**
     * Encodes a copy of the fact that the predicate it is called on is false at the next timestep
     *
     * by Definition 8
     *
     * @param timestep predicate is false on (by default placeholder "I" is used)
     * @return enc(p = false) copy
     */
    private fun String.encIsFalseCopy(timestep: String = "I"): String {
        return "(~${this}_${timestep}_u_c & ~${this}_${timestep}_t_c)"
    }

    /**
     * Encodes that the predicate it is called on is unknown at the next timestep
     *
     * by Definition 8
     *
     * @param timestep predicate is unknown on (by default placeholder "I" is used)
     * @return enc(p = unknown)
     */
    private fun String.encIsUnknown(timestep: String = "I"): String {
        return "${this}_${timestep}_u"
    }

    /**
     * Encodes the predicate (a string representation of an int) it is called on
     *
     * by Definition 9
     *
     * @param timestep predicate is encoded for (by default placeholder "i" is used)
     * @return enc(p)
     */
    private fun String.encPredicate(timestep: String = "i"): String {
        if (this == "") {
            return ""
        }
        return if (this[0] == '~') {
            when (val p = this.substring(1)) {
                "${'$'}true" -> "${'$'}false"
                "${'$'}false" -> "${'$'}true"
                else -> "((${p}_${timestep}_u & unknown) | (~${p}_${timestep}_u & ~${p}_${timestep}_t))"
            }
        } else {
            when (this) {
                "${'$'}true" -> "${'$'}true"
                "${'$'}false" -> "${'$'}false"
                else -> "((${this}_${timestep}_u & unknown) | (~${this}_${timestep}_u & ${this}_${timestep}_t))"
            }
        }
    }

    /**
     * Encodes the expression it is called on
     *
     * by Definition 9
     *
     * @param timestep the timestep the expression is encoded for (by default placeholder "i" is used)
     * @param negate if TRUE, expression is negated before being encoded
     * @return enc(exp)_i
     */
    private fun String.encExp(timestep: String = "i", negate: Boolean = false): String {
        var output = ""
        var predicate = ""
        var operator = ""
        var previousWasPredicate = false

        val expression = if(negate) {
            "(${p.parse(this).negate().nnf()})"
        } else {
            this
        }

        for (c in expression) {
            if (c == ' ' || c == '&' || c == '|' || c == '(' || c == ')') {
                if (previousWasPredicate) {
                    if (predicate != "") {
                        output += predicate.encPredicate(timestep)
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
            predicate.encPredicate(timestep)
        } else {
            output + operator
        }
    }

    /**
     * Encodes the guard it is called on
     *
     * by Definition 9
     *
     * @return encoded guard
     */
    private fun String.encGuard(): String {
        return if (this.startsWith("choice(")) {
            val choices = this.drop(7).dropLast(1)
            encGuardChoice(
                choices.substringBefore(','),
                choices.substringAfter(',').dropWhile { it == ' ' }
            )
        } else {
            "(${p.parse(this).nnf()})".encExp()
        }
    }

    /**
     * Encodes a guard choice
     *
     * by Definition 9
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
            "((${left.encExp()} | ${right.encExp(negate = true)}) & (${left.encExp()} | ${right.encExp()} | unknown))"
        }
    }

    /**
     * Encodes that all processes except [activeProcess] make an idle step from i to I
     *
     * Encoded by the constraint that the locations of the idling processes do not change from i to I
     * by Definition 10
     *
     * @param activeProcess the process that executes when we move from timestep i to I
     * @return the encoding of the idling of non-active processes
     */
    private fun encIdleAllProcessesExcept(activeProcess: Int): MutableList<String> {
        val conjunctOver = mutableListOf<String>()
        for((pId, p) in CFGS.processes.withIndex()) {
            if(activeProcess != pId) {
                val tally = p.numberOfLocations()
                for(locationId in 0..tally) {
                    for(d in 0..digitRequired(tally)) {
                        conjunctOver.add("(n_i_${pId}_${d} <=> n_I_${pId}_${d})")
                    }
                }
            }
        }
        return conjunctOver
    }

    /**
     * Counts number of locations in process it is called on
     *
     * @return the number of locations (nodes) in target process
     */
    private fun Parser.Process.numberOfLocations(): Int {
        var tally = 0
        for (transition in this.transitions) {
            if (transition.source > tally) {
                tally = transition.source
            } else if (transition.destination > tally) {
                tally = transition.source
            }
        }
        return tally + 1
    }

    /**
     * Calculates the number of bits required to name a given amount of nodes using binary
     *
     * @param numLocations the number of locations that have to be named
     * @return the amount of bits required
     */
    private fun digitRequired(numLocations: Int): Int {
        return if (numLocations == 1) {
            1
        } else {
            ceil(log2(numLocations.toDouble())).toInt()
        }
    }

    /**
     * Encodes predicate assignment, based on choice([left], [right])
     *
     * by Definition 10
     *
     * @param left left hand of choice
     * @param right right hand of choice
     * @param p the predicate that the choice expression is assigned to
     */
    private fun encAssignmentChoice(left: String, right: String, p: String): String {
        return if (left == "${'$'}true" && left == "${'$'}false") {
            p.encIsTrue()
        } else if (left == "${'$'}false" && right == "${'$'}true") {
            p.encIsFalse()
        } else if (right == "${'$'}false" && left == "${'$'}false") {
            p.encIsUnknown()
        } else {
            "((${left.encExp()} & ${p.encIsTrue()}) | " +
            "(${right.encExp()} & ${p.encIsFalse()}) | " +
            "(${("($left | $right)").encExp(negate = true).replace("unknown", "${'$'}true")} & ${p.encIsUnknown()}))"
        }
    }

    /**
     * Encodes the assignment of [expression] to the predicate it is called on
     *
     * If [expression] is not a choice() turn it into one and call [encAssignmentChoice]
     * by Definition 10
     *
     * @param expression data on how to assign the predicate
     * @return encoded assignment
     */
    private fun String.encAssignmentExpression(expression: String): String {
        return if (expression.startsWith("choice(")) {
            encAssignmentChoice(
                expression.substring(7, expression.indexOf(',')),
                expression.dropLast(1).substring(expression.indexOf(',') + 2),
                this
            )
        } else {
            encAssignmentChoice(expression, "~$expression", this)
        }
    }

    /**
     * Encodes that the values of all predicates, except [modifiedPredicates], remain unchanged from timestep i to I
     *
     * by Definition 10
     *
     * @param modifiedPredicates the predicates that are affected by the current assignment
     * @return Constraint that the non-modified predicates do not change from i to I
     */
    private fun encUnchangingPredicateValues(modifiedPredicates: MutableList<Int>): ConjunctOver<String> {
        val bigAnd = mutableListOf<String>()
        if(CFGS.predicates.isEmpty()) {
            return ConjunctOver(bigAnd)
        }
        for(p in CFGS.predicates) {
            if(!modifiedPredicates.contains(p.value)) {
                bigAnd.add(encAssignmentChoice("${p.value}", "~${p.value}", "${p.value}"))
            }
        }
        return ConjunctOver(bigAnd)
    }

    /**
     * Encodes that the operation associated with [transition] is executed form i to I
     *
     * by Definition 10
     *
     * @param transition the transition operation being encoded is derived from
     * @return the encoding of the execution of the operation
     */
    private fun encOperation(transition: Parser.Transition): Operation {
        val butChange = mutableListOf<Int>()
        val bigAnd = mutableListOf<String>()
        for(a in transition.assignments) {
            butChange.add(a.predicate)
            bigAnd.add("${a.predicate}".encAssignmentExpression(a.RHS))
        }
        bigAnd.addAll(encUnchangingPredicateValues(butChange).conjunctOver)
        return Operation(guard = transition.guard.encGuard(), assignments = ConjunctOver(bigAnd))
    }

    /**
     * Encodes a state space Transition from i to I
     *
     * by Definition 10
     *
     * @param pId the process to which the transition belongs
     * @param transition the [CFGS] transition being encoded
     * @return Encoded Transition belonging to [pId], from i to I
     */
    private fun encTransition(pId: Int, transition: Parser.Transition): Transition {
        return Transition(
            pId,
            (transition.source).encLocation(pId, "i"),
            encOperation(transition),
            (transition.destination).encLocation(pId, "I"),
            ConjunctOver(encIdleAllProcessesExcept(pId))
        )
    }

    /**
     * Encodes all possible state space Transitions from i to I
     *
     * This encoding is stored in [timestepTemplate]
     *
     * by Definition 10
     */
    private fun encodeTransitions() {
        for((pId, process) in CFGS.processes.withIndex()) {
            for (t in process.transitions) {
                timestepTemplate.disjoinOver.add(
                    encTransition(pId, t)
                )
            }


        }
        println("...CFGSEncoded")
    }

    //=====================================================================================================================
    //===================================================== Evaluator =====================================================
    //=====================================================================================================================
    /**
     *
     * The tool used to build the encoding of a bounded model checking problem [M \models \psi]_k where M corresponds to the k-bounded state space of [CFGS]
     * and \psi corresponds to the [PropertySpecification]. The k-bounded state space is encoded by k unrollings of the [timestepTemplate].
     *
     * @param property the properties of [CFGS] to be checked on [timestepTemplate]
     */
    inner class MCTaskBuilder(private val property: PropertySpecification) {

        private val predicates = mutableListOf<String>()
        init {
            if (property.type == "liveness") {
                derivePredicates()
            }
        }
        /**
         * Derives the full list of predicates that are in [timestepTemplate] and adds them to [predicates] for future use
         */
        private fun derivePredicates() {
            for (p in CFGS.predicates) {
                predicates.add("${p.value}_i_u")
                predicates.add("${p.value}_i_t")
            }
            for ((pId, process) in CFGS.processes.withIndex()) {
                for (d in 0 until digitRequired(process.numberOfLocations())) {
                    predicates.add("n_i_${pId}_${d}")
                }
            }
        }

        /**
         * Creates timestep specific formula from [timestepTemplate]
         *
         * This is an encoded timestep specific formula of the [CFGS]
         *
         * @param t timestep to create formula for
         * @return the encoded [CFGS] formula for timestep [t]
         */
        private fun formulaForTimestamp(t: Int): Formula {
            val bigOr = mutableListOf<Formula>()
            for (link in timestepTemplate.disjoinOver) {
                bigOr.add(link toFormulaWithTimestamp t)
            }
            return ff.or(bigOr)
        }

        /*private fun Formula.modifiedWith(wString: String): Formula {
            //now only works to modify locations of correctness
            println()
            println(this)
            println()
            val w = p.parse(wString)
            val disjointOver = mutableListOf(w)
            val conjunctOver = mutableListOf<Formula>()
            conjunctOver.add(ff.or(this, w.negate()))
            disjointOver.add(this.negate())
            conjunctOver.add(ff.or(disjointOver))
            return ff.and(conjunctOver)
        }*/

        /**
         * Creates timestep specific sub formula from [Transition] it is called on
         *
         * @param t timestep to create formula for
         * @return the encoded [CFGS] formula for timestep [t]
         */
        private infix fun Operation.toFormulaWithTimestamp(t: Int): Formula {
            val assignmentsFormula = mutableListOf<Formula>()
            assignmentsFormula.add(
                p.parse(guard insertTimestamp t)
            )
            assignments.conjunctOver.forEach {
                assignmentsFormula.add(p.parse(it insertTimestamp t))
            }
            return ff.and(assignmentsFormula)
        }

        /**
         * Replaces i in the string it was called on with [t] and I with ([t] + 1)
         *
         * @param t base timestep to insert into string
         * @return string with [t] inserted where placeholders were
         */
        private infix fun String.insertTimestamp(t: Int): String {
            return this.replace("i", "$t").replace("I", "${t + 1}")
        }

        /**
         * Encodes predicate expression "progress" over locations that will be used in liveness checking FG(not(progress))
         */
        private fun List<Int>.encProgressPredicate(): String {
            var progress = ""
            for (pId in this) {
                progress += property.location.encLocation(pId)
                progress += " ${property.operator} "
            }
            return progress.dropLast(3)
        }
        /**
         * by Definition?
         */
        private fun encStateRecord(): List<String> {
            val bigAnd = mutableListOf<String>()
            bigAnd.add("(rd_I <=> (re_i | rd_i))")
            predicates.distinct().forEach {
                bigAnd.add(
                    "(${it.replace("i", "I")}_c <=> (((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
                )
            }
            bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${property.processList.encProgressPredicate()})))")
            return bigAnd
        }

        /**
         * Creates the liveness location encoding of the Int it is called on
         * by Definition?
         *
         * @param t timestep formula is to be created for
         * @return [Formula] to conjunct with the encoding of each [Transition] when testing liveness
         */
        private fun Int.livenessEvaluationFormula(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            encStateRecord().forEach {
                bigAnd.add(p.parse(it insertTimestamp t))
            }
            if (property.fairnessON) {
                bigAnd.add(p.parse("(fr_I_${this} <=> (re_i | rd_i))" insertTimestamp t))
                for(pId in CFGS.processes.indices.filterNot{ it == this }) {
                    bigAnd.add(p.parse("(fr_${t + 1}_${pId} <=> fr_${t}_${pId})"))
                }
            }
            return ff.and(bigAnd)
        }

        /**
         * Creates timestep specific formula from the [Transition] it is called on
         *
         * Note, [PropertySpecification.type] is also taken into account when encoding the [Transition]
         *
         * @param [t] timestep to encode [Transition] for
         * @return encoded formula of the [Transition]
         */
        private infix fun Transition.toFormulaWithTimestamp(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            idle.conjunctOver.forEach {
                bigAnd.add(p.parse(it insertTimestamp t))
            }
            if (property.type == "liveness") {
                bigAnd.add(this.parentProcess.livenessEvaluationFormula(t))
            }
            return ff.and(
                p.parse(oldLocation insertTimestamp t),
                operation toFormulaWithTimestamp t,
                p.parse(newLocation insertTimestamp t),
                ff.and(bigAnd)
            )
        }

        /**
         * Initializes formula used in [evaluateNoOptimization]
         * by Definition 11/12?
         *
         * @return initial state of [CFGS], encoded to formula
         */
        private fun init(): Formula {
            val conjunctOver = mutableListOf<Formula>()
            for (pId in CFGS.processes.indices) {
                conjunctOver.add(p.parse(0.encLocation(pId, timestep = "0")))
                if (property.type == "liveness") {
                    conjunctOver.add(p.parse("~rd_0 & ~lv_0"))
                    conjunctOver.add(p.parse(0.encLocationCopy(pId, timestep = "0")))
                    if(property.fairnessON) {
                        conjunctOver.add(p.parse("~fr_0_${pId}"))
                    }
                }
            }
            for (predicate in CFGS.predicates) {
                val initAs: Boolean? = CFGS.init[predicate.key]
                conjunctOver.add(
                    if (initAs != null && !initAs) {
                        p.parse(("${predicate.value}").encIsFalse(timestep = "0"))
                    } else {
                        p.parse(("${predicate.value}").encIsTrue(timestep = "0"))
                    }
                )
                if(property.type == "liveness") {
                    conjunctOver.add(
                        if (initAs != null && !initAs) {
                            p.parse(("${predicate.value}").encIsFalseCopy(timestep = "0"))
                        } else {
                            p.parse(("${predicate.value}").encIsTrueCopy(timestep = "0"))
                        }
                    )
                }
            }
            return ff.and(conjunctOver)
        }

        /**
         * Encodes location it is called on as the error location for timestep [t]
         * by Definition 11/12?
         *
         * @param t timestep for which location is deemed as the error location
         * @return formula of error location for timestep [t]
         */
        private fun Int.errorLocation(t: Int = 10): Formula {
            val toJoin = mutableListOf<Formula>()
            for (pId in property.processList) {
                toJoin.add(p.parse(this.encLocation(pId, timestep = t.toString())))
            }
            return if (property.operator == "|") ff.or(toJoin) else ff.and(toJoin)
        }

        /**
         * Creates liveness property evaluation formula
         * by Definition?
         *
         * Creates the formula that turns formula for [t] of [timestepTemplate] into a satisfiable formula if and only
         * if liveness is a feature of the [CFGS] (and, if [PropertySpecification.fairnessON], fairness also) for timestep [t]
         *
         * @param [t] the timestep liveness is to be checked for
         * @return liveness property evaluation formula to be added to formula for [t] of [timestepTemplate]
         */
        private fun livenessProperty(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            bigAnd.add(p.parse("rd_$t"))
            predicates.forEach { bigAnd.add(p.parse("(${it.insertTimestamp(t)} <=> ${it.insertTimestamp(t)}_c)")) }
            bigAnd.add(p.parse("~lv_$t"))
            if(property.fairnessON) {
                for(pId in CFGS.processes.indices) {
                    bigAnd.add(p.parse("fr_${t}_$pId"))
                }
            }
            return ff.and(bigAnd)
        }

        /**
         * Ascertains the status of the literals re_i and rd_i, after being encoded and sent through the SAT solver
         *
         * @param [t] used to create the correct instance of re_i and rd_i
         * @return Pair< statusOf(re_[t]), statusOf(rd_[t]) >
         */
        private fun SortedSet<Literal>.reRdStatus(t: Int): Pair<String, String> {
            return Pair(
                if (this.contains(ff.literal("re_$t", true))) "re = true" else "re = false",
                if (this.contains(ff.literal("rd_$t", true))) "rd = true" else "rd = false"
            )
        }

        /**
         * Ascertains the status of each predicate in [CFGS], after being encoded and sent through the SAT solver
         *
         * @param [t] timestep to check predicate statuses
         * @return list of predicates and their respective statuses
         */
        private fun SortedSet<Literal>.predicateStatus(t: Int): MutableList<String> {
            val predicateStatuses = mutableListOf<String>()
            for(p in CFGS.predicates) {
                if(this.contains(ff.literal("${p.value}_${t}_u", true))) {
                    predicateStatuses.add("${p.key} = unknown")
                } else if (this.contains(ff.literal("${p.value}_${t}_t", true))) {
                    predicateStatuses.add("${p.key} = true")
                } else {
                    predicateStatuses.add("${p.key} = false")
                }
            }
            return predicateStatuses
        }

        /**
         *
         */
        private fun SortedSet<Literal>.fairnessStatus(t: Int): MutableList<String> {
            val fairnessVariableStatuses = mutableListOf<String>()
            if(!property.fairnessON) {
                fairnessVariableStatuses.add("n.a.")
                return fairnessVariableStatuses
            }
            for(pId in CFGS.processes.indices) {
                if(this.contains(ff.literal("fr_${t}_${pId}", true))) {
                    fairnessVariableStatuses.add("P$pId = fair")
                } else {
                    fairnessVariableStatuses.add("P$pId = unfair")
                }
            }
            return fairnessVariableStatuses
        }

        private fun SortedSet<Literal>.locationStatus(t: Int): MutableList<String> {
            val processLocations = mutableListOf<String>()
            for ((pId, process) in CFGS.processes.withIndex()) {
                var processLocation = ""
                for(d in 0 until digitRequired(process.numberOfLocations())) {
                    processLocation += if(this.contains(ff.literal("n_${t}_${pId}_${d}", false))) {
                        "0"
                    } else {
                        "1"
                    }
                }
                processLocations.add(processLocation)
            }
            return processLocations
        }

        private fun SortedSet<Literal>.pathInfo(bound: Int): MutableList<State> {
            val steps = mutableListOf<State>()
            for(k in 0 until bound + 1) {
                steps.add(
                    State(
                        k,
                        this.locationStatus(k),
                        this.predicateStatus(k),
                        this.fairnessStatus(k),
                        this.reRdStatus(k)
                    )
                )

            }
            return steps
        }

        private fun pathFormula(steps: MutableList<State>): Formula {
            val bigAnd = mutableListOf<Formula>()
            for((t, step) in steps.withIndex()) {
                for((pId, location) in step.locationStatus.withIndex()) {
                    bigAnd.add(
                        p.parse(location.toInt().encLocation(pId, t.toString()))
                    )
                }
            }
            return ff.and(bigAnd)
        }

        private fun String.toInt(): Int {
            var tally = 0
            for((index, c) in this.reversed().withIndex()) {
                tally += when (c) {
                    '1' -> (2.0.pow(index)).toInt()
                    '0' -> 0
                    else -> throw error("String contains invalid characters, only 1, or 0 allowed.")
                }
            }
            return tally
        }

        private fun MutableList<State>.print() {
            this.forEachIndexed { index, stepStat ->
                println("\n$index:")
                println(stepStat.locationStatus)
                println(stepStat.predicateStatus)
                println(stepStat.fairnessStatus)
                println(stepStat.reRdStatus)
            }
        }

        /*fun evaluate(bound: Int): Boolean {
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()

            var formula = init()
            for (t in 0 until bound + 1) {
                val w = "w_${t}"
                val property = if (property.type == "liveness") livenessProperty(t) else errorLocation(property.location, t)
                val correct = property.negate().cnf()

                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                println(property)
                solver.add(formula)
                solver.add(correct.modifiedWith(w))
                stepResults.add(
                    solver.sat(
                        mutableListOf(ff.literal("unknown", true), ff.literal(w, false))
                    )
                )
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printState(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    stepResults.add(
                        solver.sat(
                            mutableListOf(ff.literal("unknown", false), ff.literal(w, false))
                        )
                    )
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printState(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        printSatisfiable(startT = startTime, endT = System.nanoTime(), timestep = t)
                        return true
                    }
                }
                solver.add(ff.literal(w, true))
                formula = formulaForTimestamp(t)
            }
            printNoErrorFound(startTime, System.nanoTime(), bound)
            return false
        }*/

        private fun Formula.solveAgainWithConstraint(constraint: Formula, startIndex: Int, bound: Int) {
            println("\n=============================================================================")
            println("============= Solving Again with constraint - restarting timer ==============")
            println("=============================================================================\n")
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()
            var formula = ff.and(this, constraint)
            for (t in startIndex until bound + 1) {
                val property = if (property.type == "liveness") livenessProperty(t) else property.location.errorLocation(t)
                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                solver.reset()
                solver.add(ff.and(formula, property, p.parse("unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printState(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    val pathInfo = solver.model().literals().pathInfo(t)
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    solver.reset()
                    solver.add(ff.and(formula, property, p.parse("~unknown")))
                    stepResults.add(solver.sat())
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printState(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        val time = System.nanoTime()
                        println("\nError Path")
                        solver.model().literals().pathInfo(t).print()
                        printSatisfiable(startT = startTime, endT = time, timestep = t)
                    } else {
                        val time = System.nanoTime()
                        pathInfo.print()
                        printUnknown(startT = startTime, endT = time, timestep = t)
                    }
                    return
                }
                formula = ff.and(formula, formulaForTimestamp(t))
            }
        }

        fun evaluateNoOptimization(bound: Int) {
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()
            var formula = init()
            for (t in 0 until bound + 1) {
                val propertyFormula = if (property.type == "liveness") livenessProperty(t) else property.location.errorLocation(t)
                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                solver.reset()
                solver.add(ff.and(formula, propertyFormula, p.parse("unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printState(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    val pathInfo = solver.model().literals().pathInfo(t)
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    solver.reset()
                    solver.add(ff.and(formula, propertyFormula, p.parse("~unknown")))
                    stepResults.add(solver.sat())
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printState(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        val time = System.nanoTime()
                        println("\nError Path")
                        solver.model().literals().pathInfo(t).print()
                        printSatisfiable(startT = startTime, endT = time, timestep = t)
                        if(property.doubleTest) {
                            formula.solveAgainWithConstraint(pathFormula(solver.model().literals().pathInfo(t)), t, bound)
                        }
                    } else {
                        val time = System.nanoTime()
                        pathInfo.print()
                        printUnknown(startT = startTime, endT = time, timestep = t)
                        if(property.doubleTest) {
                            formula.solveAgainWithConstraint(pathFormula(pathInfo), t, bound)
                        }

                    }

                    return
                }
                formula = ff.and(formula, formulaForTimestamp(t))
            }
            printNoErrorFound(startTime, System.nanoTime(), bound)
        }
    }
}

