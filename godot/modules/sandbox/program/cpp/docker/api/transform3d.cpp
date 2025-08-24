/**************************************************************************/
/*  transform3d.cpp                                                       */
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

#include "transform3d.hpp"

#include "syscalls.h"

MAKE_SYSCALL(ECALL_TRANSFORM_3D_OPS, void, sys_transform3d_ops, unsigned, Transform3D_Op, ...);

Transform3D Transform3D::identity() {
	Transform3D t;
	sys_transform3d_ops(0, Transform3D_Op::IDENTITY, &t);
	return t;
}

Transform3D::Transform3D(const Vector3 &origin, const Basis &basis) {
	sys_transform3d_ops(0, Transform3D_Op::CREATE, this, &origin, basis.get_variant_index());
}

void Transform3D::assign(const Transform3D &transform) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::ASSIGN, this, transform.get_variant_index());
}

Transform3D Transform3D::inverse() const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::INVERTED, &t);
	return t;
}

void Transform3D::invert() {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::INVERTED, this);
}

Transform3D Transform3D::orthonormalized() const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::ORTHONORMALIZED, &t);
	return t;
}

void Transform3D::affine_invert() {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::AFFINE_INVERTED, this);
}

void Transform3D::rotate(const Vector3 &axis, double angle) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::ROTATED, this, axis, angle);
}

Transform3D Transform3D::rotated(const Vector3 &axis, double angle) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::ROTATED, &t, axis, angle);
	return t;
}

Transform3D Transform3D::rotated_local(const Vector3 &axis, double angle) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::ROTATED_LOCAL, &t, axis, angle);
	return t;
}

void Transform3D::scale(const Vector3 &scale) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::SCALED, this, &scale);
}

Transform3D Transform3D::scaled(const Vector3 &scale) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::SCALED, &t, &scale);
	return t;
}

Transform3D Transform3D::scaled_local(const Vector3 &scale) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::SCALED_LOCAL, &t, &scale);
	return t;
}

void Transform3D::translate(const Vector3 &offset) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::TRANSLATED, this, &offset);
}

Transform3D Transform3D::translated(const Vector3 &offset) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::TRANSLATED, &t, &offset);
	return t;
}

Transform3D Transform3D::translated_local(const Vector3 &offset) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::TRANSLATED_LOCAL, &t, &offset);
	return t;
}

Vector3 Transform3D::get_origin() const {
	Vector3 v;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::GET_ORIGIN, &v);
	return v;
}

void Transform3D::set_origin(const Vector3 &origin) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::SET_ORIGIN, this, &origin);
}

Basis Transform3D::get_basis() const {
	Basis b;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::GET_BASIS, &b);
	return b;
}

void Transform3D::set_basis(const Basis &basis) {
	sys_transform3d_ops(this->m_idx, Transform3D_Op::SET_BASIS, this, basis.get_variant_index());
}

Transform3D Transform3D::looking_at(const Vector3 &target, const Vector3 &up) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::LOOKING_AT, &t, &target, &up);
	return t;
}

Transform3D Transform3D::interpolate_with(const Transform3D &to, double weight) const {
	Transform3D t;
	sys_transform3d_ops(this->m_idx, Transform3D_Op::INTERPOLATE_WITH, &t, to.get_variant_index(), weight);
	return t;
}
