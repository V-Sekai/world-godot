/**************************************************************************/
/*  node3d.hpp                                                            */
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
#include "node.hpp"
struct Transform3D;
struct Quaternion;

// Node3D: Contains 3D transformations.
// Such as: position, rotation, scale, and skew.
struct Node3D : public Node {
	/// @brief Construct a Node3D object from an existing in-scope Node object.
	/// @param addr The address of the Node3D object.
	constexpr Node3D(uint64_t addr) :
			Node(addr) {}
	Node3D(Object obj) :
			Node(obj) {}
	Node3D(Node node) :
			Node(node) {}

	/// @brief Construct a Node3D object from a path.
	/// @param path The path to the Node3D object.
	Node3D(std::string_view path) :
			Node(path) {}

	/// @brief Get the position of the node.
	/// @return The position of the node.
	Vector3 get_position() const;
	/// @brief Set the position of the node.
	/// @param value The new position of the node.
	void set_position(const Variant &value);

	/// @brief Get the rotation of the node.
	/// @return The rotation of the node.
	Vector3 get_rotation() const;
	/// @brief Set the rotation of the node.
	/// @param value The new rotation of the node.
	void set_rotation(const Variant &value);

	/// @brief Get the scale of the node.
	/// @return The scale of the node.
	Vector3 get_scale() const;
	/// @brief Set the scale of the node.
	/// @param value The new scale of the node.
	void set_scale(const Variant &value);

	/// @brief Set the 3D transform of the node.
	/// @param value The new 3D transform of the node.
	void set_transform(const Transform3D &value);

	/// @brief Get the 3D transform of the node.
	/// @return The 3D transform of the node.
	Transform3D get_transform() const;

	/// @brief Access to the node rotation as a Quaternion. This property is ideal for tweening complex rotations.
	/// @param value The new quaternion of the node.
	void set_quaternion(const Quaternion &value);

	/// @brief Get the rotation of the node as a Quaternion.
	/// @return The rotation of the node as a Quaternion.
	Quaternion get_quaternion() const;

	/// @brief  Duplicate the node.
	/// @return A new Node3D object with the same properties and children.
	Node3D duplicate(int flags = 15) const;

	/// @brief Create a new Node3D node.
	/// @param path The path to the Node3D node.
	/// @return The Node3D node.
	static Node3D Create(std::string_view path);
};

inline Node3D Variant::as_node3d() const {
	if (get_type() == Variant::OBJECT)
		return Node3D{ uintptr_t(v.i) };
	else if (get_type() == Variant::NODE_PATH)
		return Node3D{ this->internal_fetch_string() };

	api_throw("std::bad_cast", "Variant is not a Node3D or NodePath", this);
}

inline Node3D Object::as_node3d() const {
	return Node3D{ address() };
}

inline Variant::Variant(const Node3D &node) {
	m_type = OBJECT;
	v.i = node.address();
}
