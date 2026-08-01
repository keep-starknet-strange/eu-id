package com.kss.euid.zk.sdk

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchmarkCpuListTest {

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
}
