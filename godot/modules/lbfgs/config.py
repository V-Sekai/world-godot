def can_build(env, platform):
    return not env["disable_3d"]


def configure(env):
    pass


def get_doc_classes():
    return ["LBFGSBSolver", "LBFGSBCapsuleFitterSolver"]


def get_doc_path():
    return "doc_classes"
