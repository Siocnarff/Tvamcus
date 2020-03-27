package za.ac.up.tvamcus.logbook

class TimeLog(
    private val startTime: Long = System.nanoTime(),
    private val startTimes: MutableList<Long> = mutableListOf(),
    private val endTimes: MutableList<Long> = mutableListOf(),
    private val lapTimes: MutableList<Long> = mutableListOf()
) {
    fun startLap() {
        startTimes.add(System.nanoTime())
    }
    fun endLap() {
        endTimes.add(System.nanoTime())
        lapTimes.add(endTimes.last() - startTimes.last())
    }
    fun lastLapTime(): Long {
        return lapTimes.last()
    }
    fun totalTime(): Long {
        return endTimes.last() - startTime
    }
}