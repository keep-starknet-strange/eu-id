package com.kss.euid.zk.sdk

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchmarkCpuListTest {

    @Test
    fun parsesOneAffinityRequestType() {
        assertEquals(
            BenchmarkAffinityRequest(listOf(2, 3), null),
            parseBenchmarkAffinityRequest("3+2", null),
        )
        assertEquals(
            BenchmarkAffinityRequest(null, AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER),
            parseBenchmarkAffinityRequest(null, AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER),
        )
        assertThrows(IllegalArgumentException::class.java) {
            parseBenchmarkAffinityRequest("2+3", AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER)
        }
        assertThrows(IllegalArgumentException::class.java) {
            parseBenchmarkAffinityRequest(null, "unknown")
        }
    }

    @Test
    fun selectsByCapacityAndExcludesTheMinimumTier() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1, 2, 3),
            listOf(
                cpu(0, capacity = 100, frequency = 3_000),
                cpu(1, capacity = 200, frequency = 1_000),
                cpu(2, capacity = 300, frequency = 500),
                cpu(3, capacity = 300, frequency = 400),
            ),
        )

        assertEquals(
            AffinityPolicySelection(
                selectedCpuIds = listOf(1, 2, 3),
                excludedCpuIds = listOf(0),
                topologySource = AFFINITY_TOPOLOGY_CPU_CAPACITY,
                reason = AFFINITY_REASON_READY,
            ),
            selection,
        )
    }

    @Test
    fun usesFrequencyOnlyWhenCapacityIsUnavailable() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1, 2),
            listOf(
                cpu(0, frequency = 500),
                cpu(1, frequency = 1_500),
                cpu(2, capacity = 0, frequency = 2_500),
            ),
        )

        assertEquals(
            AffinityPolicySelection(
                selectedCpuIds = listOf(1, 2),
                excludedCpuIds = listOf(0),
                topologySource = AFFINITY_TOPOLOGY_CPUINFO_MAX_FREQ,
                reason = AFFINITY_REASON_READY,
            ),
            selection,
        )
    }

    @Test
    fun capsTheSelectionAtSixHighestCapacityCpus() {
        val selection = selectExcludeMinimumCluster(
            (0..8).toList(),
            (0..8).map { id -> cpu(id, capacity = (id + 1L) * 100) },
        )

        assertEquals(listOf(3, 4, 5, 6, 7, 8), selection.selectedCpuIds)
        assertEquals(listOf(0, 1, 2), selection.excludedCpuIds)
        assertEquals(AFFINITY_TOPOLOGY_CPU_CAPACITY, selection.topologySource)
        assertEquals(AFFINITY_REASON_READY, selection.reason)
    }

    @Test
    fun failsOpenWithoutTopology() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1),
            listOf(cpu(0), cpu(1)),
        )

        assertEquals(
            AffinityPolicySelection(
                selectedCpuIds = listOf(0, 1),
                excludedCpuIds = emptyList(),
                topologySource = null,
                reason = AFFINITY_REASON_NO_TOPOLOGY,
            ),
            selection,
        )
    }

    @Test
    fun failsOpenForHomogeneousTopology() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1),
            listOf(cpu(0, capacity = 500), cpu(1, capacity = 500)),
        )

        assertEquals(
            AffinityPolicySelection(
                selectedCpuIds = listOf(0, 1),
                excludedCpuIds = emptyList(),
                topologySource = AFFINITY_TOPOLOGY_CPU_CAPACITY,
                reason = AFFINITY_REASON_HOMOGENEOUS_TOPOLOGY,
            ),
            selection,
        )
    }

    @Test
    fun usesFrequencyForIncompleteCapacityData() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1),
            listOf(
                cpu(0, capacity = 100, frequency = 1_000),
                cpu(1, frequency = 2_000),
            ),
        )

        assertEquals(listOf(1), selection.selectedCpuIds)
        assertEquals(listOf(0), selection.excludedCpuIds)
        assertEquals(AFFINITY_TOPOLOGY_CPUINFO_MAX_FREQ, selection.topologySource)
        assertEquals(AFFINITY_REASON_READY, selection.reason)
    }

    @Test
    fun failsOpenForIncompleteCapacityAndFrequencyData() {
        val selection = selectExcludeMinimumCluster(
            listOf(0, 1),
            listOf(
                cpu(0, capacity = 100, frequency = 1_000),
                cpu(1),
            ),
        )

        assertEquals(listOf(0, 1), selection.selectedCpuIds)
        assertEquals(emptyList<Int>(), selection.excludedCpuIds)
        assertEquals(null, selection.topologySource)
        assertEquals(AFFINITY_REASON_INVALID_TOPOLOGY, selection.reason)
    }

    @Test
    fun parsesLinuxAndFirebaseCpuLists() {
        assertEquals(listOf(0, 1, 2, 3, 6, 8, 9), parseCpuList("0-3,6+8-9"))
        assertEquals(listOf(1, 2), parseCpuList("2+1+2"))
    }

    @Test
    fun rejectsInvalidCpuLists() {
        for (value in listOf("", "2-1", "1--2", "1024", "1+")) {
            assertThrows(IllegalArgumentException::class.java) { parseCpuList(value) }
        }
    }

    @Test
    fun validatesRayonThreadCount() {
        assertEquals(6, parseRayonThreads("6"))
        assertEquals(16, parseRayonThreads("16"))
        for (value in listOf("", "0", "17", "six")) {
            assertThrows(IllegalArgumentException::class.java) { parseRayonThreads(value) }
        }
    }

    private fun cpu(
        id: Int,
        capacity: Long? = null,
        frequency: Long? = null,
    ): BenchmarkCpuInfo = BenchmarkCpuInfo(id, capacity, frequency)
}
