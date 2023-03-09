from code_analysis import *


class flow:

    def __init__(self):
        self.cfg = None
        self.IN = None
        self.OUT = None
        self.nodeset = None
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
        self.cfg = cfg
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
                res = [lhs, self.cfg.get_image(lhs[0])]
                self.definition.append(res)

        for node in nodeid:
            GEN[node-nodeid[0]] = set(self.gen_def(node))
            KILL[node-nodeid[0]] = set(self.kill_def(node))

        changes = True
        while changes:
            changes = False
            for node in nodeid:
                nodeindex = node-nodeid[0]
                for parent in self.cfg.get_parents(node):
                    parentindex = parent-nodeid[0]
                    self.IN[nodeindex] = self.IN[nodeindex].union(
                        self.OUT[parentindex])
                oldout[nodeindex] = self.OUT[nodeindex]
                self.OUT[nodeindex] = GEN[nodeindex].union(
                    self.IN[nodeindex] - KILL[nodeindex])
                if oldout[nodeindex] != self.OUT[nodeindex]:
                    changes = True

        return self.OUT, self.IN

    def pos_reachable_ref(self, cfg: CFG):
        self.cfg = cfg
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
                res = [lhs, self.cfg.get_image(lhs[0])]
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
            GEN[node-nodeid[0]] = set(self.gen_ref(node))
            KILL[node-nodeid[0]] = set(self.kill_ref(node))

        changes = True
        while changes:
            changes = False
            for node in nodeid:
                nodeindex = node-nodeid[0]
                for child in self.cfg.get_children(node):
                    childindex = child-nodeid[0]
                    self.OUT[nodeindex] = self.OUT[nodeindex].union(
                        self.IN[childindex])
                oldin[nodeindex] = self.IN[nodeindex]
                self.IN[nodeindex] = GEN[nodeindex].union(
                    self.OUT[nodeindex] - KILL[nodeindex])
                if oldin[nodeindex] != self.IN[nodeindex]:
                    changes = True

        return self.OUT, self.IN

        # algo
if __name__ == "__main__":
    cfgreader = CFGReader()

    cfg = cfgreader.read_cfg("../tp4/part_1/test.php.cfg.json")
    flow = flow()
    a, b = flow.pos_reaching_def(cfg)

    a, b = flow.pos_reachable_ref(cfg)
    print(a)
