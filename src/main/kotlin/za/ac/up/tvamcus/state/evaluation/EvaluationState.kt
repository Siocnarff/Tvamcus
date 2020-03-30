package za.ac.up.tvamcus.state.evaluation

data class State(
    val timestep: Int,
    val locationStatus: MutableList<String>,
    val predicateStatus: MutableList<String>,
    val fairnessStatus: MutableList<String>,
    val reRdStatus: Pair<String, String>
)