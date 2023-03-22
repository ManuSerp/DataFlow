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

                # ici on cherche le call end pour éviter de casser la propagation des definitions
                if self.cfg.get_type(node) == "CallEnd":
                    prev = self.cfg.get_call_begin(node)
                    previndex = prev-self.root
                    self.IN[nodeindex] = self.IN[nodeindex].union(
                        self.OUT[previndex])

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
                # ici on cherche le call begin pour éviter de casser la propagation des references
                if self.cfg.get_type(node) == "CallBegin":
                    next = self.cfg.get_call_end(node)
                    nextindex = next-self.root
                    self.OUT[nodeindex] = self.OUT[nodeindex].union(
                        self.IN[nextindex])

                oldin[nodeindex] = self.IN[nodeindex]
                self.IN[nodeindex] = GEN[nodeindex].union(
                    self.OUT[nodeindex] - KILL[nodeindex])
                if oldin[nodeindex] != self.IN[nodeindex]:
                    changes = True

        return self.OUT, self.IN, self.ref, self.definition


def print_defref_set(definition, ref, aref, adef, verbose=True):
    dicodef = {}
    dicoref = {}
    for i in definition:
        add = [i[1]]
        for j in aref[i[2]]:

            for k in ref:
                if k[0] == j:
                    if k[1] == i[1]:
                        add.append(j)
        dicodef[i[0][0]] = add
    if verbose:
        print("\nreference reachable for each def ( by name) \n", dicodef)
    for i in ref:
        add = [i[1]]
        for j in adef[i[0]-definition[0][3]]:
            for k in definition:
                if k[0][0] == j:
                    if k[1] == i[1]:
                        add.append(j)
        dicoref[i[0]] = add
    if verbose:
        print("\ndefinition reaching for each ref ( by name) \n", dicoref)
    return dicodef, dicoref


def nr_nd(dicodef, dicoref):
    refnondef = []
    for x in dicodef.keys():
        if len(dicodef[x]) == 1:
            refnondef.append([x, dicodef[x][0]])

    defnonref = []
    for x in dicoref.keys():
        if len(dicoref[x]) == 1:
            defnonref.append([x, dicoref[x][0]])
    return refnondef, defnonref


def prepare_query_arg_node(ast, cfg, node):
    arg = []
    rhs = ast.get_children(node)[1]
    for child in ast.get_children(rhs):
        child_n = ast.get_children(child)[0]
        if ast.get_type(child_n) == "Variable":
            arg.append([cfg.get_node_cfg_ptr(child_n), ast.get_image(child_n)])

    return arg


def flatten(l):
    return [item for sublist in l for item in sublist]


    # algo
if __name__ == "__main__":
    cfgreader = CFGReader()
    astreader = ASTReader()

    cfg = cfgreader.read_cfg("../tp4/part_1/test.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)

    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    print("\ntest:")
    print_defref_set(definition, ref, aref, adef)

    print("\nwordcount:")
    cfg = cfgreader.read_cfg("../tp4/part_1/wordcount.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    print_defref_set(definition, ref, aref, adef)

    # part 2.1
    print("\npart 2.1")
    print("\nfile1:")
    cfg = cfgreader.read_cfg("../tp4/part_2/file1.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    dicodef, dicoref = print_defref_set(
        definition, ref, aref, adef, verbose=False)

    refnondef, defnonref = nr_nd(dicodef, dicoref)
    print("\nref non def ", refnondef)
    # On detecte file name car on considere pas comme une defintion le parametre de la fonction
    print("\ndef non ref ", defnonref)

    print("\nfile2:")
    cfg = cfgreader.read_cfg("../tp4/part_2/file2.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    dicodef, dicoref = print_defref_set(
        definition, ref, aref, adef, verbose=False)
    refnondef, defnonref = nr_nd(dicodef, dicoref)
    print("\nref non def ", refnondef)
    print("\ndef non ref ", defnonref)

    print("\nfile3:")
    cfg = cfgreader.read_cfg("../tp4/part_2/file3.php.cfg.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    dicodef, dicoref = print_defref_set(
        definition, ref, aref, adef, verbose=False)
    refnondef, defnonref = nr_nd(dicodef, dicoref)
    print("\nref non def ", refnondef)
    print("\ndef non ref ", defnonref)

    # part 2.2
    print("\npart 3")
    cfg = cfgreader.read_cfg("../tp4/part_3/file.php.cfg.json")
    ast = astreader.read_ast("../tp4/part_3/file.php.ast.json")
    flow = flow_class()
    adef, bdef = flow.pos_reaching_def(cfg)
    aref, bref, ref, definition = flow.pos_reachable_ref(cfg)
    dicodef, dicoref = print_defref_set(
        definition, ref, aref, adef, verbose=False)

    total_ref_to_check = []
    for node in ast.get_node_ids():
        if ast.get_type(node) == "MethodCall" and ast.get_image(node) == "prepare_query":

            ref_to_check = prepare_query_arg_node(ast, cfg, node)
            total_ref_to_check.append(ref_to_check)
    total_ref_to_check = flatten(total_ref_to_check)
    print("\nref to check", total_ref_to_check)

    unclean = []
    for ref in total_ref_to_check:
        flag = False
        def_reaching = dicoref[ref[0]][1:]
        print("\ndef reaching for ref ", ref, " : ", def_reaching)

        for defin in def_reaching:
            flag2 = True
            ast_node = cfg.get_node_ast_ptr(defin)
            node_parent = ast.get_parents(ast_node)[0]

            if ast.get_type(node_parent) == "BinOP" and ast.get_image(node_parent) == "=":
                rhs = ast.get_children(node_parent)[1]
                if ast.get_type(rhs) == "FunctionCall" and ast.get_image(rhs) == "filter_var":
                    print("Function call: filter_var for def ",
                          def_reaching[0])
                    print("Var is filtered")
                    flag2 = False
            if flag2:
                flag = True

        if flag:
            unclean.append(ref)

    if len(unclean) == 0:
        print("\nAll variables are filtered")
    else:
        print("\nunclean variables: ", unclean)
