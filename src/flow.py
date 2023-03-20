from code_analysis import *


class flow_class:

    def __init__(self):
        self.cfg = None
        self.IN = None
        self.OUT = None
        self.nodeset = None
        self.definition = []

    def reboot(self):
        self.definition = []

    def gen_def(self, node):
        if self.cfg.get_type(node) == "BinOP" and self.cfg.get_image(node) == "=":
            lhs = self.cfg.get_parents(node)
            return lhs

        else:
            return {}

    def kill_def(self, node):
        if self.cfg.get_type(node) == "BinOP" and self.cfg.get_image(node) == "=":
            lhs = self.cfg.get_parents(node)
            name = self.cfg.get_image(lhs[0])
            res = []
            for i in self.definition:
                if i[1] == name:
                    res.append(i[0][0])
            return res

        else:
            return {}

    def gen_ref(self, node):
        if self.cfg.get_type(node) == "Variable":
            for i in self.ref:
                if i[0] == node:
                    return [i[0]]
            return {}

        else:
            return {}

    def kill_ref(self, node):
        if self.cfg.get_type(node) == "BinOP" and self.cfg.get_image(node) == "=":
            lhs = self.cfg.get_parents(node)
            name = self.cfg.get_image(lhs[0])
            res = []
            for i in self.ref:
                if i[1] == name:
                    res.append(i[0])
            return res

        else:
            return {}

    def pos_reaching_def(self, cfg: CFG):
        self.reboot()

        self.cfg = cfg
        self.root = self.cfg.get_root()

        nodeid = self.cfg.get_node_ids()
        self.nodeset = nodeid
        self.IN = [set() for i in range(len(nodeid))]
        self.OUT = [set() for i in range(len(nodeid))]
        oldout = [set() for i in range(len(nodeid))]

        GEN = [None for i in range(len(nodeid))]
        KILL = [None for i in range(len(nodeid))]

        for node in nodeid:
            if self.cfg.get_type(node) == "BinOP" and self.cfg.get_image(node) == "=":
                lhs = self.cfg.get_parents(node)
                res = [lhs, self.cfg.get_image(
                    lhs[0]), node-self.root, self.root]
                self.definition.append(res)

        for node in nodeid:
            GEN[node-self.root] = set(self.gen_def(node))
            KILL[node-self.root] = set(self.kill_def(node))

        changes = True
        while changes:
            changes = False
            for node in nodeid:
                nodeindex = node-self.root
                for parent in self.cfg.get_parents(node):
                    parentindex = parent-self.root
                    self.IN[nodeindex] = self.IN[nodeindex].union(
                        self.OUT[parentindex])
                oldout[nodeindex] = self.OUT[nodeindex]
                self.OUT[nodeindex] = GEN[nodeindex].union(
                    self.IN[nodeindex] - KILL[nodeindex])
                if oldout[nodeindex] != self.OUT[nodeindex]:
                    changes = True

        return self.OUT, self.IN

    def pos_reachable_ref(self, cfg: CFG):
        self.reboot()
        self.cfg = cfg
        self.root = self.cfg.get_root()
        nodeid = self.cfg.get_node_ids()
        self.nodeset = nodeid
        self.IN = [set() for i in range(len(nodeid))]
        self.OUT = [set() for i in range(len(nodeid))]
        oldin = [set() for i in range(len(nodeid))]

        GEN = [None for i in range(len(nodeid))]
        KILL = [None for i in range(len(nodeid))]

        for node in nodeid:
            if self.cfg.get_type(node) == "BinOP" and self.cfg.get_image(node) == "=":
                lhs = self.cfg.get_parents(node)
                res = [lhs, self.cfg.get_image(
                    lhs[0]), node-self.root, self.root]
                self.definition.append(res)

        self.ref = []
        for node in nodeid:
            if self.cfg.get_type(node) == "Variable":
                flag = True
                for i in self.definition:
                    if i[0][0] == node:
                        flag = False

                if flag:

                    self.ref.append([node, self.cfg.get_image(node)])

        for node in nodeid:
            GEN[node-self.root] = set(self.gen_ref(node))
            KILL[node-self.root] = set(self.kill_ref(node))

        changes = True
        while changes:
            changes = False
            for node in nodeid:
                nodeindex = node-self.root
                for child in self.cfg.get_children(node):
                    childindex = child-self.root
                    self.OUT[nodeindex] = self.OUT[nodeindex].union(
                        self.IN[childindex])
                oldin[nodeindex] = self.IN[nodeindex]
                self.IN[nodeindex] = GEN[nodeindex].union(
                    self.OUT[nodeindex] - KILL[nodeindex])
                if oldin[nodeindex] != self.IN[nodeindex]:
                    changes = True

        return self.OUT, self.IN, self.ref, self.definition


def print_defref_set(definition, ref, aref, adef):
    dicodef = {}
    dicoref = {}
    for i in definition:
        add = []
        for j in aref[i[2]]:

            for k in ref:
                if k[0] == j:
                    if k[1] == i[1]:
                        add.append(j)
        dicodef[i[0][0]] = add
    print("reference reachable for each def ( by name) ", dicodef)
    for i in ref:
        add = []
        for j in adef[i[0]-definition[0][3]]:
            for k in definition:
                if k[0][0] == j:
                    if k[1] == i[1]:
                        add.append(j)
        dicoref[i[0]] = add
    print("definition reaching for each ref ( by name) ", dicoref)
    return dicodef, dicoref

    # algo
if __name__ == "__main__":
    cfgreader = CFGReader()

    cfg = cfgreader.read_cfg("../tp4/part_1/test.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)

    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    print("test:")
    print_defref_set(definition, ref, aref, adef)

    print("wordcount:")
    cfg = cfgreader.read_cfg("../tp4/part_1/wordcount.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    print_defref_set(definition, ref, aref, adef)

    # part 2
    print("part 2")
    cfg = cfgreader.read_cfg("../tp4/part_2/file1.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    print_defref_set(definition, ref, aref, adef)
    print(ref)
    print(definition)
