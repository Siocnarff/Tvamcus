package za.ac.up.tvamcus.state.cfgs

data class CFGS (
    val predicates: Map<String, Int>,
    val init: Map<String, Boolean>,
    val processes: List<Process>
)

class Process(val id: Int, val transitions: MutableList<CfgsTransition>) {

    /**
     * Counts number of locations in process it is called on
     *
     * @return the number of locations (nodes) in target process
     */
    fun numberOfLocations(): Int {
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
}

data class CfgsTransition (
    val source: Int,
    val destination: Int,
    val assignments: List<Assignment>,
    var guard: String
)
data class Assignment (
    var RHS: String,

    val predicate: Int
)