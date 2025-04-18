/**************************************************************************/
/*  register_types.cpp                                                    */
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

#include "register_types.h"

#include "image_loader_svg.h"

#include <thorvg.h>

#ifdef THREADS_ENABLED
#define TVG_THREADS 1
#else
#define TVG_THREADS 0
#endif

#ifdef TOOLS_ENABLED
#include "editor/editor_node.h"
#include "editor/resource_importer_lottie.h"

static void _editor_init() {
	Ref<ResourceImporterLottie> lottie_importer;
	lottie_importer.instantiate();
	ResourceFormatImporter::get_singleton()->add_importer(lottie_importer);
}
#endif

static Ref<ImageLoaderSVG> image_loader_svg;

void initialize_svg_module(ModuleInitializationLevel p_level) {
#ifdef TOOLS_ENABLED
	if (p_level == MODULE_INITIALIZATION_LEVEL_EDITOR) {
		GDREGISTER_CLASS(ResourceImporterLottie);

		EditorNode::add_init_callback(_editor_init);
	}
#endif

	if (p_level != MODULE_INITIALIZATION_LEVEL_SCENE) {
		return;
	}

	tvg::CanvasEngine tvgEngine = tvg::CanvasEngine::Sw;

	if (tvg::Initializer::init(tvgEngine, TVG_THREADS) != tvg::Result::Success) {
		return;
	}

	image_loader_svg.instantiate();
	ImageLoader::add_image_format_loader(image_loader_svg);
}

void uninitialize_svg_module(ModuleInitializationLevel p_level) {
	if (p_level != MODULE_INITIALIZATION_LEVEL_SCENE) {
		return;
	}

	if (image_loader_svg.is_null()) {
		// It failed to initialize so it was not added.
		return;
	}

	ImageLoader::remove_image_format_loader(image_loader_svg);
	image_loader_svg.unref();
	tvg::Initializer::term(tvg::CanvasEngine::Sw);
}
