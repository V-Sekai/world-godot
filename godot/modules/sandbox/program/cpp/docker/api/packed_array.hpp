/**************************************************************************/
/*  packed_array.hpp                                                      */
/**************************************************************************/
/*                         This file is part of:                          */
/*                             GODOT ENGINE                               */
/*                        https://godotengine.org                         */
/**************************************************************************/
/* Copyright (c) 2014-present Godot Engine contributors (see AUTHORS.md). */
/* Copyright (c) 2007-2014 Juan Linietsky, Ariel Manzur.                  */
/*                                                                        */
/* Permission is hereby granted, free of charge, to any person obtaining  */
/* a copy of this software and associated documentation files (the        */
/* "Software"), to deal in the Software without restriction, including    */
/* without limitation the rights to use, copy, modify, merge, publish,    */
/* distribute, sublicense, and/or sell copies of the Software, and to     */
/* permit persons to whom the Software is furnished to do so, subject to  */
/* the following conditions:                                              */
/*                                                                        */
/* The above copyright notice and this permission notice shall be         */
/* included in all copies or substantial portions of the Software.        */
/*                                                                        */
/* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,        */
/* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF     */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. */
/* IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY   */
/* CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,   */
/* TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE      */
/* SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.                 */
/**************************************************************************/

#pragma once
#include "color.hpp"
#include "vector.hpp"
#include <cstdint>
#include <vector>
struct Variant;

/**
 * @brief A reference to a host-side Packed Array.
 * Supported:
 * - PackedByteArray
 * - PackedInt32Array
 * - PackedInt64Array
 * - PackedFloat32Array
 * - PackedFloat64Array
 * - PackedVector2Array
 * - PackedVector3Array
 * - PackedVector4Array
 * - PackedColorArray
 * - PackedStringArray
 *
 * @tparam T uint8_t, int32_t, int64_t, float, double, Vector2, Vector3, Vector4, Color or std::string.
 */
template <typename T>
struct PackedArray {
	constexpr PackedArray() {}

	/// @brief Create a PackedArray from a Variant.
	/// @param v The Variant.
	explicit PackedArray(const Variant &v);

	/// @brief Create a PackedArray from a vector of data.
	/// @param data The initial data.
	PackedArray(const std::vector<T> &data);

	/// @brief Create a PackedArray from an array of data.
	/// @param data The initial data.
	/// @param size The size of the data in elements.
	PackedArray(const T *data, size_t size);

	/// @brief Retrieve the size of the host-side array.
	/// @return size_t The size of the host-side array.
	size_t size() const { return const_cast<PackedArray *>(this)->operator()("size"); }

	/// @brief Check if the host-side array is empty.
	/// @return bool True if the host-side array is empty, false otherwise.
	bool is_empty() const { return this->size() == 0; }

	/// @brief Retrieve the host-side array data.
	/// @return std::vector<T> The host-side array data.
	std::vector<T> fetch() const;

	/// @brief Store a vector of data into the host-side array.
	/// @param data The data to store.
	void store(const std::vector<T> &data);

	/// @brief Store an array of data into the host-side array.
	/// @param data The data to store.
	void store(const T *data, size_t size);

	/// @brief Call a method on the packed array.
	/// @tparam Args The method arguments.
	template <typename... Args>
	Variant operator()(std::string_view method, Args &&...args);

	template <typename... Args>
	Variant operator()(std::string_view method, Args &&...args) const;

	/// @brief Create a PackedArray from a host-side Variant index.
	/// @param idx The host-side Variant index.
	/// @return PackedArray<T> The PackedArray.
	static PackedArray<T> from_index(unsigned idx) {
		PackedArray<T> pa{};
		pa.m_idx = idx;
		return pa;
	}
	unsigned get_variant_index() const noexcept { return m_idx; }

private:
	unsigned m_idx = INT32_MIN; // Host-side Variant index.

	static_assert(std::is_same_v<T, uint8_t> || std::is_same_v<T, int32_t> || std::is_same_v<T, int64_t> || std::is_same_v<T, float> || std::is_same_v<T, double> || std::is_same_v<T, Vector2> || std::is_same_v<T, Vector3> || std::is_same_v<T, Vector4> || std::is_same_v<T, Color> || std::is_same_v<T, std::string>,
			"PackedArray type must be uint8_t, int32_t, int64_t, float, double, Vector2, Vector3 or Color.");
};

// Aliases for common PackedArray types.
using PackedInt32Array = PackedArray<int32_t>;
using PackedInt64Array = PackedArray<int64_t>;
using PackedFloat32Array = PackedArray<float>;
using PackedFloat64Array = PackedArray<double>;
using PackedVector2Array = PackedArray<Vector2>;
using PackedVector3Array = PackedArray<Vector3>;
using PackedVector4Array = PackedArray<Vector4>;
using PackedColorArray = PackedArray<Color>;
using PackedStringArray = PackedArray<std::string>;
