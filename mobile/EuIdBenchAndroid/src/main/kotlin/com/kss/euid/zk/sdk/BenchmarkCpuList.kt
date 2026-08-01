package com.kss.euid.zk.sdk

internal const val CPU_SET_MAX_CPUS = 1024
internal const val MAX_BENCHMARK_RAYON_THREADS = 16

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
