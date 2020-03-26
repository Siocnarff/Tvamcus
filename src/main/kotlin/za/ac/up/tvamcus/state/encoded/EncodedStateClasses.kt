package za.ac.up.tvamcus.state.encoded

import za.ac.up.tvamcus.sets.ConjunctiveSet

/**
 * An encoded Control Flow Transition as an encoded guard and a list of encoded assignments
 *
 * @param guard encoded guard
 * @param assignments list of encoded assignments
 */
data class Operation(val guard: String, val assignments: ConjunctiveSet<String>)

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
    val idle: ConjunctiveSet<String>
)
