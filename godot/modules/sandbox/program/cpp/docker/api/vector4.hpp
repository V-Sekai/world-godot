/**************************************************************************/
/*  vector4.hpp                                                           */
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
#include "syscalls_fwd.hpp"
#include "vector3.hpp"
#include <cmath>

struct Vector4 {
	real_t x;
	real_t y;
	real_t z;
	real_t w;

	template <typename... Args>
	Variant operator()(std::string_view method, Args &&...args);

	METHOD(Vector4, abs);
	METHOD(Vector4, ceil);
	METHOD(Vector4, clamp);
	METHOD(Vector4, clampf);
	METHOD(Vector4, cubic_interpolate);
	METHOD(Vector4, cubic_interpolate_in_time);
	METHOD(Vector4, direction_to);
	METHOD(real_t, distance_squared_to);
	METHOD(real_t, distance_to);
	METHOD(real_t, dot);
	METHOD(Vector4, floor);
	METHOD(Vector4, inverse);
	METHOD(bool, is_equal_approx);
	METHOD(bool, is_finite);
	METHOD(bool, is_normalized);
	METHOD(bool, is_zero_approx);
	METHOD(real_t, length);
	METHOD(real_t, length_squared);
	METHOD(Vector4, lerp);
	METHOD(Vector4, max);
	METHOD(int, max_axis_index);
	METHOD(Vector4, maxf);
	METHOD(Vector4, min);
	METHOD(int, min_axis_index);
	METHOD(Vector4, minf);
	METHOD(Vector4, normalized);
	METHOD(Vector4, posmod);
	METHOD(Vector4, posmodv);
	METHOD(Vector4, round);
	METHOD(Vector4, sign);
	METHOD(Vector4, snapped);
	METHOD(Vector4, snappedf);

	Vector4 &operator+=(const Vector4 &other) {
		x += other.x;
		y += other.y;
		z += other.z;
		w += other.w;
		return *this;
	}
	Vector4 &operator-=(const Vector4 &other) {
		x -= other.x;
		y -= other.y;
		z -= other.z;
		w -= other.w;
		return *this;
	}
	Vector4 &operator*=(const Vector4 &other) {
		x *= other.x;
		y *= other.y;
		z *= other.z;
		w *= other.w;
		return *this;
	}
	Vector4 &operator/=(const Vector4 &other) {
		x /= other.x;
		y /= other.y;
		z /= other.z;
		w /= other.w;
		return *this;
	}

	bool operator==(const Vector4 &other) const {
		return __builtin_memcmp(this, &other, sizeof(Vector4)) == 0;
	}
	bool operator!=(const Vector4 &other) const {
		return !(*this == other);
	}

	constexpr Vector4() :
			x(0), y(0), z(0), w(0) {}
	constexpr Vector4(real_t val) :
			x(val), y(val), z(val), w(val) {}
	constexpr Vector4(real_t x, real_t y, real_t z, real_t w) :
			x(x), y(y), z(z), w(w) {}
	constexpr Vector4(Vector3 v, real_t w) :
			x(v.x), y(v.y), z(v.z), w(w) {}
};

inline constexpr auto operator+(const Vector4 &a, const Vector4 &b) noexcept {
	return Vector4{ a.x + b.x, a.y + b.y, a.z + b.z, a.w + b.w };
}
inline constexpr auto operator-(const Vector4 &a, const Vector4 &b) noexcept {
	return Vector4{ a.x - b.x, a.y - b.y, a.z - b.z, a.w - b.w };
}
inline constexpr auto operator*(const Vector4 &a, const Vector4 &b) noexcept {
	return Vector4{ a.x * b.x, a.y * b.y, a.z * b.z, a.w * b.w };
}
inline constexpr auto operator/(const Vector4 &a, const Vector4 &b) noexcept {
	return Vector4{ a.x / b.x, a.y / b.y, a.z / b.z, a.w / b.w };
}

inline constexpr auto operator+(const Vector4 &a, real_t b) noexcept {
	return Vector4{ a.x + b, a.y + b, a.z + b, a.w + b };
}
inline constexpr auto operator-(const Vector4 &a, real_t b) noexcept {
	return Vector4{ a.x - b, a.y - b, a.z - b, a.w - b };
}
inline constexpr auto operator*(const Vector4 &a, real_t b) noexcept {
	return Vector4{ a.x * b, a.y * b, a.z * b, a.w * b };
}
inline constexpr auto operator/(const Vector4 &a, real_t b) noexcept {
	return Vector4{ a.x / b, a.y / b, a.z / b, a.w / b };
}
