package com.kss.euid.zk.sdk

internal const val CPU_SET_MAX_CPUS = 1024
internal const val MAX_BENCHMARK_RAYON_THREADS = 16
internal const val MAX_POLICY_CPU_COUNT = 6
internal const val AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER = "exclude_min_cluster"
internal const val AFFINITY_REASON_HOMOGENEOUS_TOPOLOGY = "homogeneous_topology"
internal const val AFFINITY_REASON_INVALID_TOPOLOGY = "invalid_topology"
internal const val AFFINITY_REASON_NO_TOPOLOGY = "no_topology"
internal const val AFFINITY_REASON_READY = "ready"
internal const val AFFINITY_TOPOLOGY_CPU_CAPACITY = "cpu_capacity"
internal const val AFFINITY_TOPOLOGY_CPUINFO_MAX_FREQ = "cpuinfo_max_freq"

internal data class BenchmarkAffinityRequest(
    val explicitCpuIds: List<Int>?,
    val policy: String?,
)

internal data class BenchmarkCpuInfo(
    val id: Int,
    val capacity: Long?,
    val maximumFrequencyKhz: Long?,
)

internal data class AffinityPolicySelection(
    val selectedCpuIds: List<Int>,
    val excludedCpuIds: List<Int>,
    val topologySource: String?,
    val reason: String,
) {
    val canApply: Boolean
        get() = reason == AFFINITY_REASON_READY
}

internal fun parseBenchmarkAffinityRequest(
    explicitCpuIds: String?,
    policy: String?,
): BenchmarkAffinityRequest {
    require(explicitCpuIds == null || policy == null) {
        "affinity_cpu_ids and affinity_policy cannot be used together"
    }
    require(policy == null || policy == AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER) {
        "affinity_policy must be $AFFINITY_POLICY_EXCLUDE_MIN_CLUSTER"
    }
    return BenchmarkAffinityRequest(
        explicitCpuIds = explicitCpuIds?.let(::parseCpuList),
        policy = policy,
    )
}

internal fun selectExcludeMinimumCluster(
    allowedCpuIds: List<Int>,
    topology: List<BenchmarkCpuInfo>,
): AffinityPolicySelection {
    val allowed = allowedCpuIds.distinct().sorted()
    if (
        allowed.isEmpty() ||
        allowed.size != allowedCpuIds.size ||
        allowed.any { it !in 0 until CPU_SET_MAX_CPUS }
    ) {
        return failOpenSelection(allowed, AFFINITY_REASON_INVALID_TOPOLOGY)
    }

    val topologyById = topology.groupBy(BenchmarkCpuInfo::id)
    val allowedTopology = allowed.map { cpuId ->
        topologyById[cpuId]?.singleOrNull()
            ?: return failOpenSelection(allowed, AFFINITY_REASON_INVALID_TOPOLOGY)
    }
    val capacities = allowedTopology.map { it.capacity?.takeIf { value -> value > 0 } }
    val frequencies = allowedTopology.map {
        it.maximumFrequencyKhz?.takeIf { value -> value > 0 }
    }
    val (source, scores) = when {
        capacities.all { it != null } ->
            AFFINITY_TOPOLOGY_CPU_CAPACITY to capacities.filterNotNull()
        frequencies.all { it != null } ->
            AFFINITY_TOPOLOGY_CPUINFO_MAX_FREQ to frequencies.filterNotNull()
        capacities.all { it == null } && frequencies.all { it == null } ->
            return failOpenSelection(allowed, AFFINITY_REASON_NO_TOPOLOGY)
        else -> return failOpenSelection(allowed, AFFINITY_REASON_INVALID_TOPOLOGY)
    }

    val minimumScore = scores.min()
    if (scores.all { it == minimumScore }) {
        return failOpenSelection(
            allowed,
            AFFINITY_REASON_HOMOGENEOUS_TOPOLOGY,
            source,
        )
    }

    val selected = allowed
        .zip(scores)
        .filter { (_, score) -> score > minimumScore }
        .sortedWith(compareByDescending<Pair<Int, Long>> { it.second }.thenBy { it.first })
        .take(MAX_POLICY_CPU_COUNT)
        .map(Pair<Int, Long>::first)
        .sorted()
    val selectedSet = selected.toSet()
    return AffinityPolicySelection(
        selectedCpuIds = selected,
        excludedCpuIds = allowed.filterNot(selectedSet::contains),
        topologySource = source,
        reason = AFFINITY_REASON_READY,
    )
}

private fun failOpenSelection(
    allowedCpuIds: List<Int>,
    reason: String,
    topologySource: String? = null,
): AffinityPolicySelection = AffinityPolicySelection(
    selectedCpuIds = allowedCpuIds,
    excludedCpuIds = emptyList(),
    topologySource = topologySource,
    reason = reason,
)

internal fun parseRayonThreads(value: String): Int {
    val threads = value.toIntOrNull()
    require(threads != null && threads in 1..MAX_BENCHMARK_RAYON_THREADS) {
        "rayon_threads must be an integer from 1 through $MAX_BENCHMARK_RAYON_THREADS"
    }
    return threads
}

internal fun parseCpuList(value: String): List<Int> {
    require(value.isNotBlank()) { "CPU list must not be empty" }
    val cpus = sortedSetOf<Int>()
    value.trim().split(',', '+').forEach { rawPart ->
        val part = rawPart.trim()
        require(part.isNotEmpty()) { "CPU list contains an empty item" }
        val bounds = part.split('-', limit = 3)
        require(bounds.size <= 2) { "CPU range is invalid: $part" }
        val first = bounds[0].toIntOrNull()
            ?: throw IllegalArgumentException("CPU identifier is invalid: $part")
        val last = if (bounds.size == 2) {
            bounds[1].toIntOrNull()
                ?: throw IllegalArgumentException("CPU identifier is invalid: $part")
        } else {
            first
        }
        require(first in 0 until CPU_SET_MAX_CPUS && last in 0 until CPU_SET_MAX_CPUS) {
            "CPU identifier is outside the supported range: $part"
        }
        require(first <= last) { "CPU range is reversed: $part" }
        cpus.addAll(first..last)
    }
    return cpus.toList()
}
