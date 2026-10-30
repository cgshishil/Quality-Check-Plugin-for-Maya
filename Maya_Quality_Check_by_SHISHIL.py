# -*- coding: utf-8 -*-
"""
Maya Quality Check by SHISHIL
=============================
Model checker for  GENERAL / NAMING / MODELING / NORMALS & SHADING /
TOPOLOGY / UVs / UV PADDING.

INSTALL  : Drag this file into the Maya viewport. Done.
           It copies itself to your scripts folder, adds a
           "Maya Quality Check by SHISHIL" shelf button and opens the tool.

MANUAL   : Put the file in your Maya scripts folder, then run:
               import Maya_Quality_Check_by_SHISHIL as mqc
               mqc.show()

SUPPORT  : Minimum Maya 2017 (drag-and-drop install + Python API 2.0 UV methods).
           Runs on Python 2 and 3 and PySide / PySide2 / PySide6 (Maya 2017 -> 2025+).
           Maya 2014-2016 can only be used by manual install and are not supported.

UV PADDING : compares UV shells inside one object AND between all selected objects.
           Padding follows the texture resolution (512=4px, 1K=8px, 2K=16px,
           4K=32px, 8K=64px) and can still be overridden by hand.

SCOPE    : Something selected  -> only the selection (and children) is checked.
           Nothing selected    -> the whole scene is checked.
"""
from __future__ import print_function, division

import os
import re
import sys
import math
import shutil
import datetime
import traceback

import maya.cmds as cmds
import maya.mel as mel
import maya.api.OpenMaya as om
import maya.OpenMayaUI as omui

# --------------------------------------------------------------------------
# Qt compatibility (PySide6 -> PySide2 -> PySide)
# --------------------------------------------------------------------------
try:
    from PySide6 import QtCore, QtGui, QtWidgets
    from shiboken6 import wrapInstance
except ImportError:
    try:
        from PySide2 import QtCore, QtGui, QtWidgets
        from shiboken2 import wrapInstance
    except ImportError:
        from PySide import QtCore, QtGui
        from shiboken import wrapInstance
        QtWidgets = QtGui

try:
    string_types = (basestring,)  # noqa: F821  (Python 2)
except NameError:
    string_types = (str,)

TOOL_NAME = "Maya Quality Check by SHISHIL"
MIN_MAYA_VERSION = 2017
MIN_API_VERSION = 20170000
MODULE_NAME = "Maya_Quality_Check_by_SHISHIL"
DEFAULT_CAMERAS = ("|persp", "|top", "|front", "|side", "|back", "|left", "|bottom")

# --------------------------------------------------------------------------
# Thresholds (editable from the gear button) and UV padding settings
# --------------------------------------------------------------------------
DEFAULT_THRESH = {
    "transform": 1e-4,     # pivots / freeze tolerance
    "pole": 5,             # vertices with >= this many edges are poles
    "area": 1e-5,          # zero-area face
    "length": 1e-5,        # zero-length edge
    "uv": 1e-4,            # UV border tolerance
    "dup": 1e-4,           # duplicate vertex / face tolerance
    "overlap": 1e-3,       # overlapping face centre tolerance
    "nonplanar": 0.02,     # non planar: deviation / face size
    "flat_angle": 30.0,    # hard edge flatter than this = suspicious
    "sharp_angle": 60.0,   # soft edge sharper than this = shading artifact
}
THRESH = dict(DEFAULT_THRESH)

SETTINGS = {
    "resolution": 4096,    # texture resolution in px
    "padding": 32,         # required padding in px
    "min_spacing": 4,      # minimum shell spacing in px
    "ignore_stacked": True,
    "uv_set": None,        # None = each object's current UV set, else a UV set name
}

# Default padding (px) for every texture resolution. Changing the resolution in
# the UI writes this value into SETTINGS["padding"]; the field stays editable.
PADDING_BY_RESOLUTION = {512: 4, 1024: 8, 2048: 16, 4096: 32, 8192: 64}


def default_padding(resolution):
    """Default padding in px for a texture resolution (resolution / 128)."""
    return PADDING_BY_RESOLUTION.get(int(resolution), max(1, int(round(int(resolution) / 128.0))))


def set_resolution(resolution):
    """Select a texture resolution and reset padding to its default value."""
    SETTINGS["resolution"] = int(resolution)
    SETTINGS["padding"] = default_padding(resolution)


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------
def _ls(*a, **k):
    return cmds.ls(*a, **k) or []


def _lr(*a, **k):
    return cmds.listRelatives(*a, **k) or []


def _uniq(seq):
    seen = set()
    out = []
    for s in seq:
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out


def _short(name):
    return name.split("|")[-1]


def _dag(name):
    sel = om.MSelectionList()
    sel.add(name)
    return sel.getDagPath(0)


def _components(node, kind, ids):
    """Indices -> compact component strings: node.f[1:5]"""
    ids = sorted(set(ids))
    out = []
    start = prev = None

    def add(a, b):
        if a == b:
            out.append("%s.%s[%d]" % (node, kind, a))
        else:
            out.append("%s.%s[%d:%d]" % (node, kind, a, b))

    for i in ids:
        if start is None:
            start = prev = i
        elif i == prev + 1:
            prev = i
        else:
            add(start, prev)
            start = prev = i
    if start is not None:
        add(start, prev)
    return out


def _uf_find(parent, x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def _uf_union(parent, a, b):
    ra, rb = _uf_find(parent, a), _uf_find(parent, b)
    if ra != rb:
        parent[ra] = rb


# --------------------------------------------------------------------------
# Cached mesh data (built lazily, shared by all checks in one run)
# --------------------------------------------------------------------------
class MeshInfo(object):
    def __init__(self, shape):
        self.shape = shape
        self.dag = _dag(shape)
        self.fn = om.MFnMesh(self.dag)
        self._c = {}

    def _poly_pass(self):
        if "faces" in self._c:
            return
        faces, normals, centers = [], [], []
        it = om.MItMeshPolygon(self.dag)
        while not it.isDone():
            faces.append(list(it.getVertices()))
            n = it.getNormal(om.MSpace.kObject)
            normals.append((n.x, n.y, n.z))
            c = it.center(om.MSpace.kObject)
            centers.append((c.x, c.y, c.z))
            it.next()
        self._c["faces"], self._c["fnormals"], self._c["fcenters"] = faces, normals, centers

    def _edge_pass(self):
        if "edge_verts" in self._c:
            return
        ev, ef, es = [], [], []
        it = om.MItMeshEdge(self.dag)
        while not it.isDone():
            ev.append((it.vertexId(0), it.vertexId(1)))
            ef.append(list(it.getConnectedFaces()))
            es.append(bool(it.isSmooth))
            it.next()
        self._c["edge_verts"], self._c["edge_faces"], self._c["edge_smooth"] = ev, ef, es

    @property
    def faces(self):
        self._poly_pass()
        return self._c["faces"]

    @property
    def face_normals(self):
        self._poly_pass()
        return self._c["fnormals"]

    @property
    def face_centers(self):
        self._poly_pass()
        return self._c["fcenters"]

    @property
    def points(self):
        if "points" not in self._c:
            self._c["points"] = [(p.x, p.y, p.z) for p in self.fn.getPoints(om.MSpace.kObject)]
        return self._c["points"]

    @property
    def edge_verts(self):
        self._edge_pass()
        return self._c["edge_verts"]

    @property
    def edge_faces(self):
        self._edge_pass()
        return self._c["edge_faces"]

    @property
    def edge_smooth(self):
        self._edge_pass()
        return self._c["edge_smooth"]

    @property
    def edge_angles(self):
        """Dihedral angle (degrees) per edge, None for non two-face edges."""
        if "angles" not in self._c:
            nrm, out = self.face_normals, []
            for fl in self.edge_faces:
                if len(fl) == 2:
                    a, b = nrm[fl[0]], nrm[fl[1]]
                    d = max(-1.0, min(1.0, a[0] * b[0] + a[1] * b[1] + a[2] * b[2]))
                    out.append(math.degrees(math.acos(d)))
                else:
                    out.append(None)
            self._c["angles"] = out
        return self._c["angles"]


# --------------------------------------------------------------------------
# Scope (selection or whole scene)
# --------------------------------------------------------------------------
class Scope(object):
    def __init__(self):
        sel = _ls(selection=True, long=True, objectsOnly=True)
        self.from_selection = bool(sel)
        self._info = {}
        transforms, meshes = [], []

        if sel:
            for n in sel:
                try:
                    if cmds.nodeType(n) == "mesh":
                        if not cmds.getAttr(n + ".intermediateObject"):
                            meshes.append(n)
                        transforms.extend(_lr(n, parent=True, fullPath=True))
                    elif cmds.objectType(n, isAType="transform"):
                        transforms.append(n)
                        transforms.extend(_lr(n, allDescendents=True, type="transform", fullPath=True))
                        meshes.extend(_lr(n, allDescendents=True, type="mesh",
                                          fullPath=True, noIntermediate=True))
                except Exception:
                    pass
        else:
            transforms = _ls(type="transform", long=True)
            meshes = _ls(type="mesh", long=True, noIntermediate=True)

        self.transforms = [t for t in _uniq(transforms) if t not in DEFAULT_CAMERAS]
        self.meshes = _uniq(meshes)
        self.mesh_transforms = _uniq(
            [p for m in self.meshes for p in _lr(m, parent=True, fullPath=True)])

    def info(self, shape):
        if shape not in self._info:
            self._info[shape] = MeshInfo(shape)
        return self._info[shape]

    def describe(self):
        return u"Scope:  %s   (%d meshes)" % (
            "Selection" if self.from_selection else "Whole scene", len(self.meshes))


def _per_mesh(scope, fn):
    out = []
    for shape in scope.meshes:
        out.extend(fn(shape))
    return out


# ==========================================================================
# GENERAL
# ==========================================================================
def chk_empty_groups(scope):
    return [t for t in scope.transforms
            if cmds.nodeType(t) == "transform" and not _lr(t, children=True)]


def chk_history(scope):
    ignore = ("shadingEngine", "groupId", "objectSet", "materialInfo",
              "displayLayer", "renderLayer", "shapeEditorManager")
    bad = []
    for shape in scope.meshes:
        hist = cmds.listHistory(shape, pruneDagObjects=True) or []
        hist = [h for h in hist if cmds.nodeType(h) not in ignore]
        if hist:
            bad.extend(_lr(shape, parent=True, fullPath=True))
    return _uniq(bad)


def chk_layers(scope):
    return [t for t in scope.transforms if cmds.listConnections(t, type="displayLayer")]


def chk_parent_geometry(scope):
    bad = []
    for t in scope.mesh_transforms:
        parent = _lr(t, parent=True, fullPath=True)
        if parent and _lr(parent[0], shapes=True, type="mesh", noIntermediate=True):
            bad.append(t)
    return bad


def chk_shaders(scope):
    bad = []
    for shape in scope.meshes:
        sgs = set(cmds.listConnections(shape, type="shadingEngine") or [])
        if not sgs or sgs == set(["initialShadingGroup"]):
            bad.extend(_lr(shape, parent=True, fullPath=True))
    return _uniq(bad)


def chk_uncentered_pivots(scope):
    tol, bad = THRESH["transform"], []
    for t in scope.mesh_transforms:
        pts = cmds.xform(t, q=True, ws=True, rp=True) + cmds.xform(t, q=True, ws=True, sp=True)
        if any(abs(v) > tol for v in pts):
            bad.append(t)
    return bad


def chk_unfrozen_transforms(scope):
    tol, bad = THRESH["transform"], []
    for t in scope.mesh_transforms:
        tr = cmds.getAttr(t + ".translate")[0]
        ro = cmds.getAttr(t + ".rotate")[0]
        sc = cmds.getAttr(t + ".scale")[0]
        if any(abs(v) > tol for v in tr + ro) or any(abs(v - 1.0) > tol for v in sc):
            bad.append(t)
    return bad


# ==========================================================================
# NAMING
# ==========================================================================
def chk_duplicated_names(scope):
    counts = {}
    for t in _ls(type="transform", long=True):
        counts.setdefault(_short(t), []).append(t)
    return [t for t in scope.transforms if len(counts.get(_short(t), [])) > 1]


def chk_namespaces(scope):
    bad = [t for t in scope.transforms if ":" in _short(t)]
    for m in scope.meshes:
        if ":" in _short(m):
            bad.extend(_lr(m, parent=True, fullPath=True))
    return _uniq(bad)


def chk_shape_names(scope):
    bad = []
    for shape in scope.meshes:
        parent = _lr(shape, parent=True, fullPath=True)
        if parent and _short(shape) != _short(parent[0]) + "Shape":
            bad.append(parent[0])
    return _uniq(bad)


def chk_trailing_numbers(scope):
    return [t for t in scope.transforms if re.search(r"\d+$", _short(t))]


# ==========================================================================
# TOPOLOGY
# ==========================================================================
def chk_hard_edges(scope):
    def fn(shape):
        it, bad = om.MItMeshEdge(_dag(shape)), []
        while not it.isDone():
            if not it.isSmooth and not it.onBoundary():
                bad.append(it.index())
            it.next()
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


def chk_lamina(scope):
    def fn(shape):
        it, faces = om.MItMeshPolygon(_dag(shape)), {}
        while not it.isDone():
            faces.setdefault(tuple(sorted(it.getVertices())), []).append(it.index())
            it.next()
        return _components(shape, "f", [i for v in faces.values() if len(v) > 1 for i in v])
    return _per_mesh(scope, fn)


def chk_ngons(scope):
    def fn(shape):
        it, bad = om.MItMeshPolygon(_dag(shape)), []
        while not it.isDone():
            if it.polygonVertexCount() > 4:
                bad.append(it.index())
            it.next()
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_non_manifold_edges(scope):
    def fn(shape):
        it, bad = om.MItMeshEdge(_dag(shape)), []
        while not it.isDone():
            if it.numConnectedFaces() > 2:
                bad.append(it.index())
            it.next()
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


def chk_open_edges(scope):
    def fn(shape):
        it, bad = om.MItMeshEdge(_dag(shape)), []
        while not it.isDone():
            if it.onBoundary():
                bad.append(it.index())
            it.next()
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


def chk_poles(scope):
    def fn(shape):
        it, bad, limit = om.MItMeshVertex(_dag(shape)), [], int(THRESH["pole"])
        while not it.isDone():
            if it.numConnectedEdges() >= limit:
                bad.append(it.index())
            it.next()
        return _components(shape, "vtx", bad)
    return _per_mesh(scope, fn)


def chk_starlike(scope):
    """Concave / star-shaped faces."""
    def fn(shape):
        it, bad = om.MItMeshPolygon(_dag(shape)), []
        while not it.isDone():
            n = it.polygonVertexCount()
            if n > 3:
                pts = it.getPoints(om.MSpace.kObject)
                nrm = it.getNormal(om.MSpace.kObject)
                for i in range(n):
                    a, b, c = pts[i - 1], pts[i], pts[(i + 1) % n]
                    e1 = om.MVector(b.x - a.x, b.y - a.y, b.z - a.z)
                    e2 = om.MVector(c.x - b.x, c.y - b.y, c.z - b.z)
                    if (e1 ^ e2) * nrm < -1e-8:
                        bad.append(it.index())
                        break
            it.next()
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_triangles(scope):
    def fn(shape):
        it, bad = om.MItMeshPolygon(_dag(shape)), []
        while not it.isDone():
            if it.polygonVertexCount() == 3:
                bad.append(it.index())
            it.next()
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_zero_area_faces(scope):
    def fn(shape):
        it, bad = om.MItMeshPolygon(_dag(shape)), []
        while not it.isDone():
            if it.getArea(om.MSpace.kWorld) < THRESH["area"]:
                bad.append(it.index())
            it.next()
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_zero_length_edges(scope):
    def fn(shape):
        it, bad = om.MItMeshEdge(_dag(shape)), []
        while not it.isDone():
            if it.length(om.MSpace.kWorld) < THRESH["length"]:
                bad.append(it.index())
            it.next()
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


# ==========================================================================
# MODELING
# ==========================================================================
def chk_duplicates(scope):
    """Vertices at the same position + faces occupying identical positions."""
    def fn(shape):
        info = scope.info(shape)
        scale = 1.0 / max(THRESH["dup"], 1e-9)
        vkeys = [(int(round(p[0] * scale)), int(round(p[1] * scale)), int(round(p[2] * scale)))
                 for p in info.points]
        groups = {}
        for i, k in enumerate(vkeys):
            groups.setdefault(k, []).append(i)
        bad_v = [i for g in groups.values() if len(g) > 1 for i in g]
        fgroups = {}
        for f, verts in enumerate(info.faces):
            fgroups.setdefault(tuple(sorted(vkeys[v] for v in verts)), []).append(f)
        bad_f = [i for g in fgroups.values() if len(g) > 1 for i in g]
        return _components(shape, "vtx", bad_v) + _components(shape, "f", bad_f)
    return _per_mesh(scope, fn)


def chk_non_manifold_geo(scope):
    """Non-manifold edges (3+ faces) and non-manifold vertices (bow-ties)."""
    def fn(shape):
        info = scope.info(shape)
        ev, ef = info.edge_verts, info.edge_faces
        bad_e = [e for e, fl in enumerate(ef) if len(fl) > 2]
        vert_edges = {}
        for e, (a, b) in enumerate(ev):
            vert_edges.setdefault(a, []).append(e)
            vert_edges.setdefault(b, []).append(e)
        bad_v = []
        for v, edges in vert_edges.items():
            faces = set()
            for e in edges:
                faces.update(ef[e])
            if len(faces) < 2:
                continue
            parent = dict((f, f) for f in faces)
            for e in edges:
                fl = ef[e]
                for k in range(1, len(fl)):
                    _uf_union(parent, fl[0], fl[k])
            if len(set(_uf_find(parent, f) for f in faces)) > 1:
                bad_v.append(v)
        return _components(shape, "e", bad_e) + _components(shape, "vtx", bad_v)
    return _per_mesh(scope, fn)


def chk_internal_faces(scope):
    """Faces whose every edge is shared by more than two faces (hidden inside)."""
    def fn(shape):
        info = scope.info(shape)
        faces = info.faces
        cnt = [0] * len(faces)
        for fl in info.edge_faces:
            if len(fl) > 2:
                for f in set(fl):
                    cnt[f] += 1
        return _components(shape, "f", [f for f, c in enumerate(cnt) if c and c >= len(faces[f])])
    return _per_mesh(scope, fn)


def chk_overlapping_faces(scope):
    """Faces sharing the same centre and plane (z-fighting)."""
    def fn(shape):
        info = scope.info(shape)
        scale = 1.0 / max(THRESH["overlap"], 1e-9)
        groups = {}
        for f, c in enumerate(info.face_centers):
            groups.setdefault((int(round(c[0] * scale)), int(round(c[1] * scale)),
                               int(round(c[2] * scale))), []).append(f)
        nrm, bad = info.face_normals, set()
        for g in groups.values():
            for i in range(len(g)):
                for j in range(i + 1, len(g)):
                    a, b = nrm[g[i]], nrm[g[j]]
                    if abs(a[0] * b[0] + a[1] * b[1] + a[2] * b[2]) > 0.999:
                        bad.add(g[i])
                        bad.add(g[j])
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_isolated_vertices(scope):
    def fn(shape):
        it, bad = om.MItMeshVertex(_dag(shape)), []
        while not it.isDone():
            if it.numConnectedEdges() == 0:
                bad.append(it.index())
            it.next()
        return _components(shape, "vtx", bad)
    return _per_mesh(scope, fn)


def chk_self_intersections(scope):
    """Edges that pierce faces of the same mesh (ray test per edge)."""
    def fn(shape):
        info = scope.info(shape)
        fnm, pts = info.fn, info.points
        ev, ef = info.edge_verts, info.edge_faces
        try:
            accel = fnm.autoUniformGridParams()
        except Exception:
            accel = None
        bad, edge_tol = set(), 1e-4
        for e, (a, b) in enumerate(ev):
            pa, pb = pts[a], pts[b]
            d = om.MVector(pb[0] - pa[0], pb[1] - pa[1], pb[2] - pa[2])
            length = d.length()
            if length < 1e-7:
                continue
            d.normalize()
            src = om.MFloatPoint(pa[0], pa[1], pa[2])
            dirv = om.MFloatVector(d.x, d.y, d.z)
            try:
                res = fnm.allIntersections(src, dirv, om.MSpace.kObject, length, False,
                                           None, None, False, accel, 1e-6, False)
            except Exception:
                res = fnm.allIntersections(src, dirv, om.MSpace.kObject, length, False)
            if not res or not res[0]:
                continue
            params, hit_faces, own = res[1], res[2], set(ef[e])
            for k in range(len(hit_faces)):
                if params[k] <= edge_tol or params[k] >= length - edge_tol:
                    continue
                if hit_faces[k] in own:
                    continue
                bad.add(hit_faces[k])
                bad.update(own)
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_disconnected(scope):
    """Mesh made of several shells: everything except the largest shell."""
    def fn(shape):
        info = scope.info(shape)
        nf = len(info.faces)
        if nf == 0:
            return []
        parent = list(range(nf))
        for fl in info.edge_faces:
            for k in range(1, len(fl)):
                _uf_union(parent, fl[0], fl[k])
        shells = {}
        for f in range(nf):
            shells.setdefault(_uf_find(parent, f), []).append(f)
        if len(shells) < 2:
            return []
        largest = max(shells.values(), key=len)
        bad = [f for g in shells.values() if g is not largest for f in g]
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


# ==========================================================================
# NORMALS & SHADING
# ==========================================================================
def chk_reversed_faces(scope):
    """Faces whose winding disagrees with their neighbours / the shell's outside."""
    def fn(shape):
        info = scope.info(shape)
        faces, pts = info.faces, info.points
        ev, ef = info.edge_verts, info.edge_faces
        nf = len(faces)
        pair_to_e = {}
        for e, (a, b) in enumerate(ev):
            pair_to_e[(a, b) if a < b else (b, a)] = e
        edge_dirs = [[] for _ in ev]
        for f, verts in enumerate(faces):
            n = len(verts)
            for k in range(n):
                a, b = verts[k], verts[(k + 1) % n]
                e = pair_to_e.get((a, b) if a < b else (b, a))
                if e is not None:
                    edge_dirs[e].append((f, 1 if a < b else -1))
        face_edges = [[] for _ in range(nf)]
        for e, dirs in enumerate(edge_dirs):
            for f, _s in dirs:
                face_edges[f].append(e)

        flip = {}
        bad = []
        for seed in range(nf):
            if seed in flip:
                continue
            flip[seed] = 0
            shell, stack = [seed], [seed]
            while stack:
                f = stack.pop()
                for e in face_edges[f]:
                    if len(edge_dirs[e]) != 2:
                        continue
                    (f1, s1), (f2, s2) = edge_dirs[e]
                    if f1 == f:
                        mine, other, os_ = s1, f2, s2
                    else:
                        mine, other, os_ = s2, f1, s1
                    if other in flip:
                        continue
                    eff = mine * (1 - 2 * flip[f])
                    flip[other] = 1 if eff * os_ == 1 else 0
                    shell.append(other)
                    stack.append(other)
            if len(shell) < 2:
                continue
            ones = [f for f in shell if flip[f] == 1]
            zeros = [f for f in shell if flip[f] == 0]
            closed = all(len(edge_dirs[e]) == 2 for f in shell for e in face_edges[f])
            if closed:
                vol = 0.0
                for f in shell:
                    v = faces[f]
                    p0 = pts[v[0]]
                    sgn = 1 - 2 * flip[f]
                    for k in range(1, len(v) - 1):
                        p1, p2 = pts[v[k]], pts[v[k + 1]]
                        cx = p1[1] * p2[2] - p1[2] * p2[1]
                        cy = p1[2] * p2[0] - p1[0] * p2[2]
                        cz = p1[0] * p2[1] - p1[1] * p2[0]
                        vol += sgn * (p0[0] * cx + p0[1] * cy + p0[2] * cz) / 6.0
                bad.extend(ones if vol >= 0 else zeros)
            else:
                bad.extend(ones if len(ones) <= len(zeros) else zeros)
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_vertex_normals(scope):
    """Vertex normals pointing away (>90 deg) from their face normal."""
    def fn(shape):
        info = scope.info(shape)
        counts, ids = info.fn.getNormalIds()
        normals = info.fn.getNormals(om.MSpace.kObject)
        counts, ids = list(counts), list(ids)
        bad, offset = set(), 0
        for f, c in enumerate(counts):
            fnorm, verts = info.face_normals[f], info.faces[f]
            for k in range(c):
                vn = normals[ids[offset + k]]
                if vn.x * fnorm[0] + vn.y * fnorm[1] + vn.z * fnorm[2] < 0.0:
                    bad.add(verts[k])
            offset += c
        return _components(shape, "vtx", bad)
    return _per_mesh(scope, fn)


def chk_normals_onoff(scope):
    """Shape-level normal switches: 'Opposite' on, or normal display left on."""
    bad = []
    for shape in scope.meshes:
        try:
            flagged = cmds.getAttr(shape + ".opposite") or cmds.getAttr(shape + ".displayNormal")
        except Exception:
            flagged = False
        if flagged:
            bad.extend(_lr(shape, parent=True, fullPath=True))
    return _uniq(bad)


def chk_hard_soft(scope):
    """Hard edges lying on an almost flat surface (unnecessary hard edges)."""
    def fn(shape):
        info = scope.info(shape)
        flat = THRESH["flat_angle"]
        bad = [e for e, ang in enumerate(info.edge_angles)
               if ang is not None and not info.edge_smooth[e] and ang < flat]
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


def chk_locked_normals(scope):
    def fn(shape):
        info = scope.info(shape)
        fnm = info.fn
        locked = set(i for i in range(fnm.numNormals) if fnm.isNormalLocked(i))
        if not locked:
            return []
        counts, ids = fnm.getNormalIds()
        counts, ids = list(counts), list(ids)
        bad, offset = set(), 0
        for f, c in enumerate(counts):
            for k in range(c):
                if ids[offset + k] in locked:
                    bad.add(info.faces[f][k])
            offset += c
        return _components(shape, "vtx", bad)
    return _per_mesh(scope, fn)


def chk_non_planar(scope):
    def fn(shape):
        info = scope.info(shape)
        pts, tol, bad = info.points, THRESH["nonplanar"], []
        for f, verts in enumerate(info.faces):
            if len(verts) < 4:
                continue
            p = [pts[v] for v in verts]
            n = info.face_normals[f]
            cx = sum(q[0] for q in p) / len(p)
            cy = sum(q[1] for q in p) / len(p)
            cz = sum(q[2] for q in p) / len(p)
            dev = max(abs((q[0] - cx) * n[0] + (q[1] - cy) * n[1] + (q[2] - cz) * n[2]) for q in p)
            size = max(math.sqrt((q[0] - cx) ** 2 + (q[1] - cy) ** 2 + (q[2] - cz) ** 2) for q in p)
            if size > 1e-9 and dev / size > tol:
                bad.append(f)
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_shading_artifacts(scope):
    """Soft edges across a sharp angle (cause dark gradients / pinching)."""
    def fn(shape):
        info = scope.info(shape)
        sharp = THRESH["sharp_angle"]
        bad = [e for e, ang in enumerate(info.edge_angles)
               if ang is not None and info.edge_smooth[e] and ang > sharp]
        return _components(shape, "e", bad)
    return _per_mesh(scope, fn)


# ==========================================================================
# UVs
# ==========================================================================
def _face_uvs(mesh):
    counts, ids = mesh.getAssignedUVs()
    us, vs = mesh.getUVs()
    counts, ids, us, vs = list(counts), list(ids), list(us), list(vs)
    faces, offset = [], 0
    for c in counts:
        faces.append(ids[offset:offset + c])
        offset += c
    return faces, us, vs


def chk_cross_border(scope):
    def fn(shape):
        faces, us, vs = _face_uvs(om.MFnMesh(_dag(shape)))
        tol, bad = THRESH["uv"], []
        for f, ids in enumerate(faces):
            if not ids:
                continue
            fu = [us[i] for i in ids]
            fv = [vs[i] for i in ids]
            if (math.floor(max(fu) - tol) > math.floor(min(fu) + tol) or
                    math.floor(max(fv) - tol) > math.floor(min(fv) + tol)):
                bad.append(f)
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_missing_uvs(scope):
    def fn(shape):
        mesh = om.MFnMesh(_dag(shape))
        faces, _, _ = _face_uvs(mesh)
        if len(faces) < mesh.numPolygons:
            return _components(shape, "f", range(mesh.numPolygons))
        return _components(shape, "f", [f for f, ids in enumerate(faces) if not ids])
    return _per_mesh(scope, fn)


def chk_on_border(scope):
    def fn(shape):
        faces, us, vs = _face_uvs(om.MFnMesh(_dag(shape)))
        tol = THRESH["uv"]
        used = set(i for ids in faces for i in ids)
        bad = [i for i in used
               if abs(us[i] - round(us[i])) < tol or abs(vs[i] - round(vs[i])) < tol]
        return _components(shape, "map", bad)
    return _per_mesh(scope, fn)


def _tri_overlap(t1, t2, eps=1e-7):
    """Separating-axis test for two 2D triangles. Touching = no overlap."""
    for tri in (t1, t2):
        for i in range(3):
            x1, y1 = tri[i]
            x2, y2 = tri[(i + 1) % 3]
            ax, ay = -(y2 - y1), (x2 - x1)
            p1 = [ax * x + ay * y for x, y in t1]
            p2 = [ax * x + ay * y for x, y in t2]
            if max(p1) <= min(p2) + eps or max(p2) <= min(p1) + eps:
                return False
    return True


def chk_self_penetrating_uvs(scope):
    """Faces whose UVs overlap other faces of the same mesh."""
    cell = 0.05

    def fn(shape):
        faces, us, vs = _face_uvs(om.MFnMesh(_dag(shape)))
        polys, bbox, grid = {}, {}, {}
        for f, ids in enumerate(faces):
            if len(ids) < 3:
                continue
            pts = [(us[i], vs[i]) for i in ids]
            tris = []
            for k in range(1, len(pts) - 1):
                a, b, c = pts[0], pts[k], pts[k + 1]
                area = abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1]))
                if area > 1e-12:
                    tris.append((a, b, c))
            if not tris:
                continue
            polys[f] = tris
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            bb = (min(xs), min(ys), max(xs), max(ys))
            bbox[f] = bb
            for gx in range(int(math.floor(bb[0] / cell)), int(math.floor(bb[2] / cell)) + 1):
                for gy in range(int(math.floor(bb[1] / cell)), int(math.floor(bb[3] / cell)) + 1):
                    grid.setdefault((gx, gy), []).append(f)

        bad, done = set(), set()
        for members in grid.values():
            n = len(members)
            for i in range(n):
                for j in range(i + 1, n):
                    a, b = members[i], members[j]
                    key = (a, b) if a < b else (b, a)
                    if key in done:
                        continue
                    done.add(key)
                    if a in bad and b in bad:
                        continue
                    if set(faces[a]) & set(faces[b]):
                        continue
                    ba, bb2 = bbox[a], bbox[b]
                    if ba[2] <= bb2[0] or bb2[2] <= ba[0] or ba[3] <= bb2[1] or bb2[3] <= ba[1]:
                        continue
                    hit = False
                    for ta in polys[a]:
                        for tb in polys[b]:
                            if _tri_overlap(ta, tb):
                                hit = True
                                break
                        if hit:
                            break
                    if hit:
                        bad.add(a)
                        bad.add(b)
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


def chk_uv_range(scope):
    def fn(shape):
        faces, us, vs = _face_uvs(om.MFnMesh(_dag(shape)))
        lo, hi = -THRESH["uv"], 1.0 + THRESH["uv"]
        bad = []
        for f, ids in enumerate(faces):
            for i in ids:
                if us[i] < lo or us[i] > hi or vs[i] < lo or vs[i] > hi:
                    bad.append(f)
                    break
        return _components(shape, "f", bad)
    return _per_mesh(scope, fn)


# ==========================================================================
# UV PADDING
# ==========================================================================
def _pt_seg_d2(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    l2 = dx * dx + dy * dy
    t = 0.0 if l2 <= 1e-20 else max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / l2))
    cx, cy = ax + t * dx, ay + t * dy
    return (px - cx) ** 2 + (py - cy) ** 2


def _ccw(ax, ay, bx, by, cx, cy):
    return (cy - ay) * (bx - ax) - (by - ay) * (cx - ax)


def _seg_dist(a0, a1, b0, b1):
    """Distance between segments a0-a1 and b0-b1 (each a (u, v) tuple)."""
    d1 = _ccw(b0[0], b0[1], b1[0], b1[1], a0[0], a0[1])
    d2 = _ccw(b0[0], b0[1], b1[0], b1[1], a1[0], a1[1])
    d3 = _ccw(a0[0], a0[1], a1[0], a1[1], b0[0], b0[1])
    d4 = _ccw(a0[0], a0[1], a1[0], a1[1], b1[0], b1[1])
    if d1 * d2 < 0 and d3 * d4 < 0:
        return 0.0
    m = min(_pt_seg_d2(a0[0], a0[1], b0[0], b0[1], b1[0], b1[1]),
            _pt_seg_d2(a1[0], a1[1], b0[0], b0[1], b1[0], b1[1]),
            _pt_seg_d2(b0[0], b0[1], a0[0], a0[1], a1[0], a1[1]),
            _pt_seg_d2(b1[0], b1[1], a0[0], a0[1], a1[0], a1[1]))
    return math.sqrt(m)


STACK_TOL = 1e-5          # UV distance under which two shells count as identical (stacked)
_UVPAD_USED_SETS = {}     # {mesh shape: UV set read by the last UV padding run}


def _uv_set_names(fnm, shape):
    try:
        return list(fnm.getUVSetNames())
    except Exception:
        return list(cmds.polyUVSet(shape, q=True, allUVSets=True) or [])


def _current_uv_set(fnm, shape):
    try:
        return fnm.currentUVSetName()
    except Exception:
        cur = cmds.polyUVSet(shape, q=True, currentUVSet=True)
        return cur[0] if cur else None


def _read_uv_layout(fnm, shape, uv_set):
    """(faces, us, vs, shell_ids) of ONE explicit UV set (never the 'current' one by accident)."""
    try:
        counts, flat_ids = fnm.getAssignedUVs(uv_set)
        us, vs = fnm.getUVs(uv_set)
        _n, shell_ids = fnm.getUvShellsIds(uv_set)
    except TypeError:
        # API builds whose methods take no UV set argument can only read the current set.
        if uv_set != _current_uv_set(fnm, shape):
            raise RuntimeError("this Maya version can only read the current UV set")
        counts, flat_ids = fnm.getAssignedUVs()
        us, vs = fnm.getUVs()
        _n, shell_ids = fnm.getUvShellsIds()
    counts, flat_ids = list(counts), list(flat_ids)
    faces, offset = [], 0
    for c in counts:
        faces.append(flat_ids[offset:offset + c])
        offset += c
    return faces, list(us), list(vs), list(shell_ids)


def _collect_uv_layouts(scope):
    """Read the UV layout of every mesh in scope, freshly, on every call.

    Returns (layouts, problems). `problems` are transforms whose UVs could not be
    read for the chosen UV set; they are reported as errors, never skipped silently.
    """
    wanted = SETTINGS.get("uv_set")
    layouts, problems, notes = [], [], []
    _UVPAD_USED_SETS.clear()
    for shape in scope.meshes:
        transform = (_lr(shape, parent=True, fullPath=True) or [shape])[0]
        try:
            try:
                cmds.dgdirty(shape)
            except Exception:
                pass
            fnm = om.MFnMesh(_dag(shape))
            if wanted:
                if wanted not in _uv_set_names(fnm, shape):
                    problems.append(transform)
                    notes.append("%s has no UV set '%s'" % (_short(transform), wanted))
                    continue
                uv_set = wanted
            else:
                uv_set = _current_uv_set(fnm, shape)
            faces, us, vs, shells = _read_uv_layout(fnm, shape, uv_set)
        except Exception as exc:
            problems.append(transform)
            notes.append("%s: could not read UVs (%s)" % (_short(transform), exc))
            continue
        if not any(faces):
            notes.append("%s has no UVs in '%s' (not compared)" % (_short(transform), uv_set))
            continue
        _UVPAD_USED_SETS[shape] = uv_set
        layouts.append({"shape": shape, "uv_set": uv_set, "faces": faces,
                        "us": us, "vs": vs, "shells": shells})

    used = sorted(set(l["uv_set"] for l in layouts))
    if not wanted and len(used) > 1:
        notes.append("objects use different current UV sets (%s); pick one in 'UV Set' "
                     "to compare a single layout" % ", ".join(used))
    if notes:
        cmds.warning("UV padding: " + " | ".join(notes[:6]) +
                     (" | ..." if len(notes) > 6 else ""))
    return layouts, problems


def _build_shells(layout):
    """{shell_id: ({uv_id: (u, v)}, set_of_(uv_a, uv_b)_edges)} for one object."""
    us, vs, shells = layout["us"], layout["vs"], layout["shells"]
    n, out, seen = min(len(us), len(vs), len(shells)), {}, set()
    for ids in layout["faces"]:
        m = len(ids)
        if m < 2:
            continue
        for k in range(m):
            a, b = ids[k], ids[(k + 1) % m]
            if a == b or not (0 <= a < n and 0 <= b < n):
                continue
            key = (a, b) if a < b else (b, a)
            if key in seen:
                continue
            seen.add(key)
            pts, edges = out.setdefault(shells[a], ({}, set()))
            pts[a] = (us[a], vs[a])
            pts[b] = (us[b], vs[b])
            edges.add(key)
    return out


def _find_uv_match(grid, pts, taken, u, v, cell):
    cx, cy = int(math.floor(u / cell)), int(math.floor(v / cell))
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            for cand in grid.get((cx + dx, cy + dy), ()):
                if cand in taken:
                    continue
                pu, pv = pts[cand]
                if abs(pu - u) <= STACK_TOL and abs(pv - v) <= STACK_TOL:
                    return cand
    return None


def _shells_stacked(sa, sb):
    """True only when both shells are the SAME UV geometry (every vertex and every
    edge matches within STACK_TOL). Similar bounding boxes are not enough."""
    pa, ea = sa
    pb, eb = sb
    if len(pa) != len(pb) or len(ea) != len(eb):
        return False
    cell = STACK_TOL * 4.0
    grid = {}
    for uid, (u, v) in pa.items():
        grid.setdefault((int(math.floor(u / cell)), int(math.floor(v / cell))), []).append(uid)
    match, taken = {}, set()
    for uid, (u, v) in pb.items():
        found = _find_uv_match(grid, pa, taken, u, v, cell)
        if found is None:
            return False
        taken.add(found)
        match[uid] = found
    for a, b in eb:
        ma, mb = match[a], match[b]
        if ((ma, mb) if ma < mb else (mb, ma)) not in ea:
            return False
    return True


def _multi_mesh_shell_proximity(layouts, dist, ignore_stacked):
    """{layout_index: set(uv_ids)} of shell edges closer than `dist` (UV units) to a
    DIFFERENT shell. Shells are keyed by (object, shell id), so shells inside one
    object and shells of different objects are all compared in the same UV space."""
    if dist <= 0 or not layouts:
        return {}
    shells, segs = {}, []
    for li, lay in enumerate(layouts):
        for sid, rec in _build_shells(lay).items():
            key = (li, sid)
            shells[key] = rec
            pts = rec[0]
            for a, b in rec[1]:
                segs.append((li, a, b, key, pts[a], pts[b]))
    if not segs:
        return {}

    cell, half, dist2 = max(float(dist), 1.0 / 256.0), dist * 0.5, dist * dist
    grid, first_cell, boxes = {}, [], []
    for i, (_li, _a, _b, _key, p0, p1) in enumerate(segs):
        bx0, bx1 = min(p0[0], p1[0]), max(p0[0], p1[0])
        by0, by1 = min(p0[1], p1[1]), max(p0[1], p1[1])
        boxes.append((bx0, by0, bx1, by1))
        # two segments closer than `dist` have bounding boxes closer than `dist` on both
        # axes, so growing every box by dist/2 guarantees they share at least one cell
        gx0, gx1 = int(math.floor((bx0 - half) / cell)), int(math.floor((bx1 + half) / cell))
        gy0, gy1 = int(math.floor((by0 - half) / cell)), int(math.floor((by1 + half) / cell))
        first_cell.append((gx0, gy0))
        for gx in range(gx0, gx1 + 1):
            for gy in range(gy0, gy1 + 1):
                grid.setdefault((gx, gy), []).append(i)

    bad, stacked = {}, {}
    for (gx, gy), members in grid.items():
        n = len(members)
        for x in range(n):
            i = members[x]
            si, bi, fi = segs[i], boxes[i], first_cell[i]
            for y in range(x + 1, n):
                j = members[y]
                # a pair shares several cells: evaluate it in exactly one of them
                fj = first_cell[j]
                if gx != (fi[0] if fi[0] > fj[0] else fj[0]) or gy != (fi[1] if fi[1] > fj[1] else fj[1]):
                    continue
                sj, bj = segs[j], boxes[j]
                if si[3] == sj[3]:
                    continue
                dx = max(0.0, bi[0] - bj[2], bj[0] - bi[2])
                dy = max(0.0, bi[1] - bj[3], bj[1] - bi[3])
                if dx * dx + dy * dy >= dist2:
                    continue
                set_i, set_j = bad.get(si[0]), bad.get(sj[0])
                if (set_i and set_j and si[1] in set_i and si[2] in set_i and
                        sj[1] in set_j and sj[2] in set_j):
                    continue                      # both edges already reported
                if _seg_dist(si[4], si[5], sj[4], sj[5]) >= dist:
                    continue
                if ignore_stacked:
                    pair = (si[3], sj[3]) if si[3] < sj[3] else (sj[3], si[3])
                    st = stacked.get(pair)
                    if st is None:
                        st = _shells_stacked(shells[pair[0]], shells[pair[1]])
                        stacked[pair] = st
                    if st:
                        continue
                bad.setdefault(si[0], set()).update((si[1], si[2]))
                bad.setdefault(sj[0], set()).update((sj[1], sj[2]))
    return bad


def _uvpad_errors(scope, dist):
    layouts, problems = _collect_uv_layouts(scope)
    bad = _multi_mesh_shell_proximity(layouts, dist, SETTINGS["ignore_stacked"])
    out = []
    for li, lay in enumerate(layouts):
        if li in bad:
            out.extend(_components(lay["shape"], "map", bad[li]))
    return out + problems


def chk_uv_padding(scope):
    return _uvpad_errors(scope, SETTINGS["padding"] / float(SETTINGS["resolution"]))


def chk_uv_spacing(scope):
    return _uvpad_errors(scope, SETTINGS["min_spacing"] / float(SETTINGS["resolution"]))


def chk_uv_border_padding(scope):
    """UVs closer to a UV tile border than half the required padding."""
    limit = SETTINGS["padding"] / float(SETTINGS["resolution"]) * 0.5
    layouts, problems = _collect_uv_layouts(scope)
    out = []
    for lay in layouts:
        us, vs = lay["us"], lay["vs"]
        used = set(i for ids in lay["faces"] for i in ids if 0 <= i < len(us))
        bad = [i for i in used
               if min(abs(us[i] - round(us[i])), abs(vs[i] - round(vs[i]))) < limit]
        out.extend(_components(lay["shape"], "map", bad))
    return out + problems


def _activate_uv_sets(errors):
    """Make the UV set that was checked the current one, so 'map[]' components select
    the right UVs (map indices always refer to the object's current UV set)."""
    for shape, uv_set in list(_UVPAD_USED_SETS.items()):
        if not any(e.startswith(shape + ".") for e in errors):
            continue
        try:
            cur = cmds.polyUVSet(shape, q=True, currentUVSet=True)
            if cur and cur[0] != uv_set:
                cmds.polyUVSet(shape, currentUVSet=True, uvSet=uv_set)
                cmds.warning("UV padding: current UV set of %s switched to '%s' "
                             "to match the checked layout." % (_short(shape), uv_set))
        except Exception:
            pass


def _scope_uv_sets(scope, limit=500):
    names = []
    for shape in scope.meshes[:limit]:
        try:
            names.extend(cmds.polyUVSet(shape, q=True, allUVSets=True) or [])
        except Exception:
            pass
    return sorted(set(names))


# --------------------------------------------------------------------------
# Check registry  (group, key, label, tooltip, function)
# --------------------------------------------------------------------------
CHECKS = [
    # GENERAL
    ("GENERAL", "empty_groups", "Empty Groups", "Groups that contain nothing.", chk_empty_groups),
    ("GENERAL", "history", "History", "Meshes with construction history.", chk_history),
    ("GENERAL", "layers", "Layers", "Objects assigned to display layers.", chk_layers),
    ("GENERAL", "parent_geometry", "Parent Geometry", "Geometry parented under other geometry.", chk_parent_geometry),
    ("GENERAL", "shaders", "Shaders", "Meshes with no shader or only the default lambert1.", chk_shaders),
    ("GENERAL", "uncentered_pivots", "Uncentered Pivots", "Pivots that are not at the world origin.", chk_uncentered_pivots),
    ("GENERAL", "unfrozen_transforms", "Unfrozen Transforms", "Non-zero translate/rotate or scale different from 1.", chk_unfrozen_transforms),
    # NAMING
    ("NAMING", "duplicated_names", "Duplicated Names", "Transforms sharing the same short name.", chk_duplicated_names),
    ("NAMING", "namespaces", "Namespaces", "Nodes that live in a namespace.", chk_namespaces),
    ("NAMING", "shape_names", "Shape Names", "Shape name must be <TransformName>Shape.", chk_shape_names),
    ("NAMING", "trailing_numbers", "Trailing Numbers", "Names that end with a number (pCube1).", chk_trailing_numbers),
    # MODELING
    ("MODELING", "m_duplicates", "Duplicate Faces / Vertices", "Vertices at the same position and faces occupying identical positions.", chk_duplicates),
    ("MODELING", "m_nonmanifold", "Non Manifold Geometry", "Edges shared by 3+ faces and bow-tie (non-manifold) vertices.", chk_non_manifold_geo),
    ("MODELING", "m_lamina", "Lamina Faces", "Faces sharing exactly the same vertices.", chk_lamina),
    ("MODELING", "m_internal", "Internal Faces", "Faces hidden inside the mesh (all edges shared by 3+ faces).", chk_internal_faces),
    ("MODELING", "m_zero_area", "Zero Area Faces", "Faces with (almost) no area.", chk_zero_area_faces),
    ("MODELING", "m_zero_length", "Zero Length Edges", "Edges with (almost) no length.", chk_zero_length_edges),
    ("MODELING", "m_overlap", "Overlapping Faces", "Faces sharing the same centre and plane (z-fighting).", chk_overlapping_faces),
    ("MODELING", "m_isolated", "Isolated Vertices", "Vertices that are not connected to any edge.", chk_isolated_vertices),
    ("MODELING", "m_open", "Open Borders (Holes)", "Border edges around holes / open meshes.", chk_open_edges),
    ("MODELING", "m_intersect", "Mesh Intersections (Self Intersect)", "Faces pierced by edges of the same mesh. Can be slow on dense meshes.", chk_self_intersections),
    ("MODELING", "m_disconnected", "Disconnected Mesh Components", "Meshes made of several separate shells (all but the largest are reported).", chk_disconnected),
    # NORMALS & SHADING
    ("NORMALS", "n_reversed", "Face Normals (Reversed)", "Faces whose winding disagrees with their neighbours / the outside of a closed shell.", chk_reversed_faces),
    ("NORMALS", "n_vertex", "Vertex Normals (Inconsistent)", "Vertex normals pointing more than 90 degrees away from their face.", chk_vertex_normals),
    ("NORMALS", "n_onoff", "Normals On/Off (Check if Normals are unlocked)", "Shape normal switches: 'Opposite' enabled or normals display left on.", chk_normals_onoff),
    ("NORMALS", "n_hardsoft", "Hard / Soft Edges Check", "Hard edges on an almost flat surface (angle below the flat-angle threshold).", chk_hard_soft),
    ("NORMALS", "n_locked", "Locked Normals", "Vertex normals that are locked.", chk_locked_normals),
    ("NORMALS", "n_nonplanar", "Non Planar Faces", "Faces whose vertices do not lie on one plane.", chk_non_planar),
    ("NORMALS", "n_artifacts", "Shading Artifacts (Edge Smoothing)", "Soft edges across a sharp angle (above the sharp-angle threshold).", chk_shading_artifacts),
    # TOPOLOGY
    ("TOPOLOGY", "hard_edges", "Hard Edges", "Hard (non-smooth) edges, border edges excluded.", chk_hard_edges),
    ("TOPOLOGY", "lamina", "Lamina", "Faces sharing exactly the same vertices.", chk_lamina),
    ("TOPOLOGY", "ngons", "Ngons", "Faces with more than 4 sides.", chk_ngons),
    ("TOPOLOGY", "non_manifold_edges", "Non Manifold Edges", "Edges shared by more than 2 faces.", chk_non_manifold_edges),
    ("TOPOLOGY", "open_edges", "Open Edges", "Border edges (holes / open meshes).", chk_open_edges),
    ("TOPOLOGY", "poles", "Poles", "Vertices with many edges (see settings, default 5+).", chk_poles),
    ("TOPOLOGY", "starlike", "Starlike", "Concave / star-shaped faces.", chk_starlike),
    ("TOPOLOGY", "triangles", "Triangles", "Faces with exactly 3 sides.", chk_triangles),
    ("TOPOLOGY", "zero_area_faces", "Zero Area Faces", "Faces with (almost) no area.", chk_zero_area_faces),
    ("TOPOLOGY", "zero_length_edges", "Zero Length Edges", "Edges with (almost) no length.", chk_zero_length_edges),
    # UVS
    ("UVS", "cross_border", "Cross Border", "Faces whose UVs straddle a UV tile border.", chk_cross_border),
    ("UVS", "missing_uvs", "Missing UVs", "Faces without UVs.", chk_missing_uvs),
    ("UVS", "on_border", "On Border", "UVs that sit exactly on a UV tile border.", chk_on_border),
    ("UVS", "self_penetrating", "Self Penetrating UVs", "Faces whose UVs overlap other faces.", chk_self_penetrating_uvs),
    ("UVS", "uv_range", "UV Range", "UVs outside the 0-1 space.", chk_uv_range),
    # UV PADDING
    ("UVPAD", "uvp_padding", "UV Padding Check", "UV shells closer to each other than the Required Padding (in pixels at the chosen texture resolution).", chk_uv_padding),
    ("UVPAD", "uvp_spacing", "Minimum Shell Spacing", "UV shells closer to each other than the Minimum Shell Spacing (touching / bleeding shells).", chk_uv_spacing),
    ("UVPAD", "uvp_border", "Shell Border Padding", "UVs closer to a UV tile border than half of the Required Padding.", chk_uv_border_padding),
]

# group id, title, accent colour, icon
SECTIONS = [
    ("GENERAL", "GENERAL", "#2d8cff", "folder"),
    ("NAMING", "NAMING", "#ff9f1c", "tag"),
    ("MODELING", "MODELING", "#1ec8e6", "cube"),
    ("NORMALS", "NORMALS & SHADING", "#ff3d8b", "ring"),
    ("TOPOLOGY", "TOPOLOGY", "#2ee27a", "warning"),
    ("UVS", "UVs", "#a45cff", "checker"),
    ("UVPAD", "UV PADDING", "#ff4f87", "grid"),
]

# name, checks switched OFF, (resolution, padding) or None  (padding = PADDING_BY_RESOLUTION)
PRESETS = [
    ("Character / Creature", ["triangles", "hard_edges", "m_intersect", "m_disconnected", "n_hardsoft"], (4096, 32)),
    ("Hard Surface / Prop", ["poles", "hard_edges", "n_hardsoft", "n_artifacts", "m_disconnected"], (2048, 16)),
    ("Environment / Modular", ["poles", "hard_edges", "m_disconnected", "uncentered_pivots", "m_intersect"], (2048, 16)),
    ("Game Ready (Strict)", ["triangles"], (2048, 16)),
    ("All Checks", [], None),
]


# --------------------------------------------------------------------------
# Painted icons (no external image files needed)
# --------------------------------------------------------------------------
def make_icon(kind, color="#ffffff", size=26, hole="#18212b"):
    Qt = QtCore.Qt
    pm = QtGui.QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QtGui.QPainter(pm)
    p.setRenderHint(QtGui.QPainter.Antialiasing)
    c = QtGui.QColor(color)
    pen = QtGui.QPen(c)
    pen.setWidthF(2.0)
    pen.setCapStyle(Qt.RoundCap)
    p.setPen(pen)
    p.setBrush(Qt.NoBrush)
    s = float(size)
    F = QtCore.QPointF

    if kind == "folder":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        p.drawRoundedRect(QtCore.QRectF(3, 9, s - 6, s - 13), 2, 2)
        p.drawRoundedRect(QtCore.QRectF(3, 5, 10, 6), 2, 2)
    elif kind == "tag":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        p.drawPolygon(QtGui.QPolygonF([F(4, 4), F(14, 4), F(s - 3, 13), F(14, s - 3), F(4, 13)]))
        p.setBrush(QtGui.QColor(hole))
        p.drawEllipse(F(9, 9), 2.2, 2.2)
    elif kind == "cube":
        cx, cy, r = s / 2, s / 2, s / 2 - 3
        pts = [F(cx + r * math.cos(math.radians(60 * i - 90)),
                 cy + r * math.sin(math.radians(60 * i - 90))) for i in range(6)]
        fill = QtGui.QColor(c)
        fill.setAlpha(110)
        p.setBrush(fill)
        p.drawPolygon(QtGui.QPolygonF(pts))
        p.drawLine(F(cx, cy), pts[1])
        p.drawLine(F(cx, cy), pts[3])
        p.drawLine(F(cx, cy), pts[5])
    elif kind == "ring":
        pen.setWidthF(3.0)
        p.setPen(pen)
        p.drawArc(QtCore.QRectF(5, 5, s - 10, s - 10), 60 * 16, 270 * 16)
    elif kind == "warning":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        p.drawPolygon(QtGui.QPolygonF([F(s / 2, 3), F(s - 3, s - 4), F(3, s - 4)]))
        p.setPen(QtGui.QPen(QtGui.QColor(hole), 2.2, Qt.SolidLine, Qt.RoundCap))
        p.drawLine(F(s / 2, 10), F(s / 2, 16))
        p.drawPoint(F(s / 2, 20))
    elif kind == "checker":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        q = (s - 6) / 3.0
        for i in range(3):
            for j in range(3):
                if (i + j) % 2 == 0:
                    p.drawRect(QtCore.QRectF(3 + i * q, 3 + j * q, q, q))
    elif kind == "grid":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        q = (s - 8) / 3.0
        for i in range(3):
            for j in range(3):
                p.drawRect(QtCore.QRectF(3 + i * (q + 1), 3 + j * (q + 1), q - 0.5, q - 0.5))
    elif kind == "select":
        pen.setWidthF(1.3)
        pen.setStyle(Qt.DashLine)
        p.setPen(pen)
        p.drawRect(QtCore.QRectF(2.5, 2.5, s - 5, s - 5))
    elif kind == "gear":
        pen.setWidthF(1.8)
        p.setPen(pen)
        p.drawEllipse(F(s / 2, s / 2), s * 0.22, s * 0.22)
        pen.setWidthF(2.6)
        p.setPen(pen)
        for i in range(8):
            a = math.radians(45 * i)
            p.drawLine(F(s / 2 + math.cos(a) * s * 0.32, s / 2 + math.sin(a) * s * 0.32),
                       F(s / 2 + math.cos(a) * s * 0.42, s / 2 + math.sin(a) * s * 0.42))
    elif kind == "dots":
        p.setPen(Qt.NoPen)
        p.setBrush(c)
        for i in range(3):
            p.drawEllipse(F(s * (0.25 + 0.25 * i), s / 2), 1.8, 1.8)
    elif kind == "logo":
        p.setPen(Qt.NoPen)
        p.setBrush(QtGui.QColor("#16b8a6"))
        p.drawRoundedRect(QtCore.QRectF(1, 1, s - 2, s - 2), 5, 5)
        f = QtGui.QFont()
        f.setBold(True)
        f.setPixelSize(int(s * 0.62))
        p.setFont(f)
        p.setPen(QtGui.QColor("#ffffff"))
        p.drawText(QtCore.QRectF(0, 0, s, s), Qt.AlignCenter, "M")
    p.end()
    return pm


# --------------------------------------------------------------------------
# Custom widgets
# --------------------------------------------------------------------------
class CheckBoxBlue(QtWidgets.QCheckBox):
    def __init__(self, parent=None):
        super(CheckBoxBlue, self).__init__(parent)
        self.setFixedSize(22, 22)
        self.setCursor(QtCore.Qt.PointingHandCursor)

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.Antialiasing)
        r = QtCore.QRectF(2, 2, 18, 18)
        if self.isChecked():
            p.setPen(QtCore.Qt.NoPen)
            p.setBrush(QtGui.QColor("#2d8cff"))
            p.drawRoundedRect(r, 3, 3)
            pen = QtGui.QPen(QtGui.QColor("#ffffff"), 2.2)
            pen.setCapStyle(QtCore.Qt.RoundCap)
            pen.setJoinStyle(QtCore.Qt.RoundJoin)
            p.setPen(pen)
            p.drawLine(QtCore.QPointF(6, 11.5), QtCore.QPointF(9.5, 15))
            p.drawLine(QtCore.QPointF(9.5, 15), QtCore.QPointF(16, 7.5))
        else:
            p.setPen(QtGui.QPen(QtGui.QColor("#6a7889"), 1.5))
            p.setBrush(QtGui.QColor("#101820"))
            p.drawRoundedRect(r, 3, 3)
        p.end()


class SelectButton(QtWidgets.QPushButton):
    """'Select Error Nodes' button with the dashed-box icon on the right."""
    def __init__(self, parent=None):
        super(SelectButton, self).__init__("Select Error Nodes", parent)
        self._hover = False
        self._on = make_icon("select", "#d6e4f2", 16)
        self._off = make_icon("select", "#566170", 16)
        self.setCursor(QtCore.Qt.PointingHandCursor)

    def enterEvent(self, e):
        self._hover = True
        self.update()
        super(SelectButton, self).enterEvent(e)

    def leaveEvent(self, e):
        self._hover = False
        self.update()
        super(SelectButton, self).leaveEvent(e)

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.Antialiasing)
        on = self.isEnabled()
        if on:
            bg, fg, border = ("#3b5f86" if self._hover else "#2d4a6b"), "#eaf2fa", "#4a76a6"
        else:
            bg, fg, border = "#1b232d", "#5b6673", "#242e3a"
        p.setPen(QtGui.QPen(QtGui.QColor(border), 1))
        p.setBrush(QtGui.QColor(bg))
        p.drawRoundedRect(QtCore.QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5), 3, 3)
        p.setPen(QtGui.QColor(fg))
        p.drawText(QtCore.QRectF(10, 0, self.width() - 36, self.height()),
                   QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft, self.text())
        p.drawPixmap(self.width() - 24, (self.height() - 16) // 2, self._on if on else self._off)
        p.end()


class ClickFrame(QtWidgets.QFrame):
    on_click = None

    def mousePressEvent(self, event):
        if self.on_click:
            self.on_click()
        super(ClickFrame, self).mousePressEvent(event)


class SectionFrame(QtWidgets.QFrame):
    ARROW_OPEN = u"\u25BC"
    ARROW_CLOSED = u"\u25B6"

    def __init__(self, title, color, icon_kind, parent=None):
        super(SectionFrame, self).__init__(parent)
        self.setObjectName("section")
        lay = QtWidgets.QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)

        head = ClickFrame()
        head.setObjectName("sechead")
        head.setCursor(QtCore.Qt.PointingHandCursor)
        head.setFixedHeight(34)
        hl = QtWidgets.QHBoxLayout(head)
        hl.setContentsMargins(0, 0, 12, 0)
        hl.setSpacing(10)
        bar = QtWidgets.QFrame()
        bar.setFixedWidth(5)
        bar.setStyleSheet("background:%s; border-radius:2px;" % color)
        icon = QtWidgets.QLabel()
        icon.setPixmap(make_icon(icon_kind, color, 24))
        title_lbl = QtWidgets.QLabel(title)
        title_lbl.setStyleSheet("font-size:13px; font-weight:bold; letter-spacing:1px; color:#f2f6fa;")
        self.arrow = QtWidgets.QLabel(self.ARROW_OPEN)
        self.arrow.setStyleSheet("color:#dfe6ee; font-size:12px;")
        hl.addWidget(bar)
        hl.addWidget(icon)
        hl.addWidget(title_lbl)
        hl.addStretch(1)
        hl.addWidget(self.arrow)
        lay.addWidget(head)

        self.body = QtWidgets.QWidget()
        self.body_layout = QtWidgets.QVBoxLayout(self.body)
        self.body_layout.setContentsMargins(10, 4, 10, 8)
        self.body_layout.setSpacing(2)
        lay.addWidget(self.body)
        head.on_click = self.toggle

    def toggle(self):
        show = not self.body.isVisible()
        self.body.setVisible(show)
        self.arrow.setText(self.ARROW_OPEN if show else self.ARROW_CLOSED)


STATE_BG = {"idle": "#222d39", "pass": "#1d5a3b", "fail": "#8f1f30", "error": "#8a5a14"}


class CheckRow(QtWidgets.QWidget):
    def __init__(self, check, run_cb, select_cb, parent=None):
        super(CheckRow, self).__init__(parent)
        self.group, self.key, self.label_text, self.tip, self.func = check
        self.errors = None

        lay = QtWidgets.QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)

        self.checkbox = CheckBoxBlue()
        self.checkbox.setChecked(True)
        self.label = QtWidgets.QLabel(self.label_text)
        self.label.setFixedHeight(24)
        self.label.setToolTip(self.tip)
        self.run_btn = QtWidgets.QPushButton("Run")
        self.run_btn.setObjectName("runBtn")
        self.run_btn.setFixedSize(78, 24)
        self.select_btn = SelectButton()
        self.select_btn.setFixedSize(190, 24)
        self.select_btn.setEnabled(False)

        lay.addWidget(self.checkbox)
        lay.addWidget(self.label, 1)
        lay.addWidget(self.run_btn)
        lay.addWidget(self.select_btn)

        self.run_btn.clicked.connect(lambda: run_cb(self))
        self.select_btn.clicked.connect(lambda: select_cb(self))
        self._paint("idle")

    def _paint(self, state, text=None):
        self.label.setText(text or self.label_text)
        self.label.setStyleSheet(
            "background:%s; color:#eef3f8; padding-left:8px; border-radius:2px;" % STATE_BG[state])

    @property
    def state(self):
        if self.errors is None:
            return "idle"
        return "fail" if self.errors else "pass"

    def set_result(self, errors):
        self.errors = errors
        if errors:
            self._paint("fail", u"%s  (%d)" % (self.label_text, len(errors)))
            self.label.setToolTip(u"%s\n\n%s%s" % (
                self.tip, u"\n".join(errors[:15]), u"\n..." if len(errors) > 15 else u""))
            self.select_btn.setEnabled(True)
        else:
            self._paint("pass")
            self.label.setToolTip(self.tip + u"\n\nPassed.")
            self.select_btn.setEnabled(False)

    def set_exception(self, msg):
        self.errors = None
        self._paint("error", u"%s  (error)" % self.label_text)
        self.label.setToolTip(u"Check could not run:\n" + msg)
        self.select_btn.setEnabled(False)

    def reset(self):
        self.errors = None
        self._paint("idle")
        self.label.setToolTip(self.tip)
        self.select_btn.setEnabled(False)


class UVPaddingSettings(QtWidgets.QFrame):
    """Texture resolution buttons, padding spin boxes and stacked-UV option."""
    RES = [("512", 512), ("1K", 1024), ("2K", 2048), ("4K", 4096), ("8K", 8192)]
    CURRENT_SET_TEXT = "Current UV Set (each object)"

    def __init__(self, on_change, parent=None):
        super(UVPaddingSettings, self).__init__(parent)
        self.setObjectName("uvsettings")
        self._on_change = on_change
        grid = QtWidgets.QGridLayout(self)
        grid.setContentsMargins(10, 8, 10, 8)
        grid.setHorizontalSpacing(12)
        grid.setVerticalSpacing(6)

        def lbl(text):
            l = QtWidgets.QLabel(text)
            l.setStyleSheet("color:#dfe6ee;")
            return l

        grid.addWidget(lbl("Texture Resolution"), 0, 0)
        res_lay = QtWidgets.QHBoxLayout()
        res_lay.setSpacing(4)
        self.group = QtWidgets.QButtonGroup(self)
        self.group.setExclusive(True)
        self.res_buttons = {}
        for text, val in self.RES:
            b = QtWidgets.QPushButton(text)
            b.setCheckable(True)
            b.setObjectName("resBtn")
            b.setFixedHeight(26)
            b.clicked.connect(lambda checked=False, v=val: self._set_res(v))
            self.group.addButton(b)
            self.res_buttons[val] = b
            res_lay.addWidget(b)
        grid.addLayout(res_lay, 0, 1)

        grid.addWidget(lbl("Required Padding"), 1, 0)
        self.pad_spin = QtWidgets.QSpinBox()
        self.pad_spin.setRange(1, 1024)
        self.pad_spin.setFixedWidth(90)
        pl = QtWidgets.QHBoxLayout()
        pl.addWidget(self.pad_spin)
        pl.addWidget(lbl("px"))
        pl.addStretch(1)
        grid.addLayout(pl, 1, 1)

        grid.addWidget(lbl("Minimum Shell Spacing"), 2, 0)
        self.min_spin = QtWidgets.QSpinBox()
        self.min_spin.setRange(0, 512)
        self.min_spin.setFixedWidth(90)
        ml = QtWidgets.QHBoxLayout()
        ml.addWidget(self.min_spin)
        ml.addWidget(lbl("px"))
        ml.addStretch(1)
        grid.addLayout(ml, 2, 1)

        grid.addWidget(lbl("Ignore Stacked UVs"), 3, 0)
        self.stack_cb = CheckBoxBlue()
        sl = QtWidgets.QHBoxLayout()
        sl.addWidget(self.stack_cb)
        sl.addStretch(1)
        grid.addLayout(sl, 3, 1)

        grid.addWidget(lbl("UV Set"), 4, 0)
        self.uvset_combo = QtWidgets.QComboBox()
        self.uvset_combo.setToolTip("Which UV set is compared on every object. 'Current' uses the "
                                    "UV set that is active on each object.")
        self.uvset_combo.addItem(self.CURRENT_SET_TEXT)
        grid.addWidget(self.uvset_combo, 4, 1)

        self.hint = QtWidgets.QLabel()
        self.hint.setStyleSheet("color:#8fa3b8; font-size:11px;")
        self.hint.setWordWrap(True)
        grid.addWidget(self.hint, 5, 0, 1, 2)
        grid.setColumnStretch(1, 1)

        self.refresh_from_settings()
        self.pad_spin.valueChanged.connect(self._spin_changed)
        self.min_spin.valueChanged.connect(self._spin_changed)
        self.stack_cb.toggled.connect(self._spin_changed)
        self.uvset_combo.currentIndexChanged.connect(self._uvset_changed)

    def refresh_from_settings(self):
        res = SETTINGS["resolution"]
        if res in self.res_buttons:
            self.res_buttons[res].setChecked(True)
        for w in (self.pad_spin, self.min_spin, self.stack_cb):
            w.blockSignals(True)
        self.pad_spin.setValue(SETTINGS["padding"])
        self.min_spin.setValue(SETTINGS["min_spacing"])
        self.stack_cb.setChecked(SETTINGS["ignore_stacked"])
        for w in (self.pad_spin, self.min_spin, self.stack_cb):
            w.blockSignals(False)
        self._update_hint()

    def _update_hint(self):
        res = float(SETTINGS["resolution"])
        self.hint.setText(
            u"At %dpx:  padding %d px = %.4f UV   |   min spacing %d px = %.4f UV" % (
                SETTINGS["resolution"], SETTINGS["padding"], SETTINGS["padding"] / res,
                SETTINGS["min_spacing"], SETTINGS["min_spacing"] / res))

    def _set_res(self, value):
        # New resolution -> default padding for it (4K=32px, 2K=16px ...).
        # The padding field stays editable, so the value can be overridden by hand.
        set_resolution(value)
        self.pad_spin.blockSignals(True)
        self.pad_spin.setValue(SETTINGS["padding"])
        self.pad_spin.blockSignals(False)
        self._update_hint()
        self._on_change()

    def set_uv_sets(self, names):
        """Fill the UV Set list (keeps the current choice, even if the set is not in scope)."""
        chosen = SETTINGS.get("uv_set")
        names = list(names)
        if chosen and chosen not in names:
            names.append(chosen)
        self.uvset_combo.blockSignals(True)
        self.uvset_combo.clear()
        self.uvset_combo.addItem(self.CURRENT_SET_TEXT)
        for n in names:
            self.uvset_combo.addItem(n)
        index = names.index(chosen) + 1 if chosen else 0
        self.uvset_combo.setCurrentIndex(index)
        self.uvset_combo.blockSignals(False)

    def _uvset_changed(self, *_args):
        index = self.uvset_combo.currentIndex()     # signal argument differs between PySide versions
        SETTINGS["uv_set"] = None if index <= 0 else self.uvset_combo.itemText(index)
        self._on_change()

    def _spin_changed(self, *_a):
        SETTINGS["padding"] = self.pad_spin.value()
        SETTINGS["min_spacing"] = self.min_spin.value()
        SETTINGS["ignore_stacked"] = self.stack_cb.isChecked()
        self._update_hint()
        self._on_change()


class ThresholdDialog(QtWidgets.QDialog):
    FIELDS = [
        ("pole", "Pole: min. edges on a vertex", 3, 12, 0, 1),
        ("area", "Zero area face (max area)", 0, 1, 7, 1e-5),
        ("length", "Zero length edge (max length)", 0, 1, 7, 1e-5),
        ("transform", "Pivot / freeze tolerance", 0, 1, 7, 1e-4),
        ("dup", "Duplicate vertex tolerance", 0, 1, 7, 1e-4),
        ("overlap", "Overlapping face centre tolerance", 0, 1, 7, 1e-3),
        ("uv", "UV border tolerance", 0, 1, 7, 1e-4),
        ("nonplanar", "Non planar (deviation / face size)", 0, 1, 4, 0.005),
        ("flat_angle", "Hard edge flatter than (deg)", 0, 180, 1, 1.0),
        ("sharp_angle", "Soft edge sharper than (deg)", 0, 180, 1, 1.0),
    ]

    def __init__(self, parent=None):
        super(ThresholdDialog, self).__init__(parent)
        self.setWindowTitle("Check Settings")
        self.spins = {}
        lay = QtWidgets.QVBoxLayout(self)
        form = QtWidgets.QFormLayout()
        for key, text, lo, hi, dec, step in self.FIELDS:
            sp = QtWidgets.QDoubleSpinBox()
            sp.setDecimals(dec)
            sp.setRange(lo, hi)
            sp.setSingleStep(step)
            sp.setValue(THRESH[key])
            sp.setMinimumWidth(110)
            self.spins[key] = sp
            form.addRow(text, sp)
        lay.addLayout(form)
        btns = QtWidgets.QHBoxLayout()
        reset = QtWidgets.QPushButton("Reset Defaults")
        ok = QtWidgets.QPushButton("Apply")
        cancel = QtWidgets.QPushButton("Cancel")
        btns.addWidget(reset)
        btns.addStretch(1)
        btns.addWidget(ok)
        btns.addWidget(cancel)
        lay.addLayout(btns)
        reset.clicked.connect(self._reset)
        ok.clicked.connect(self._apply)
        cancel.clicked.connect(self.reject)

    def _reset(self):
        for key, sp in self.spins.items():
            sp.setValue(DEFAULT_THRESH[key])

    def _apply(self):
        for key, sp in self.spins.items():
            THRESH[key] = int(sp.value()) if key == "pole" else sp.value()
        self.accept()


STYLE = u"""
QDialog#MayaQualityCheckUI { background: #121820; }
QLabel { color: #dfe6ee; }
QToolTip { background: #0d1218; color: #e6edf5; border: 1px solid #34465a; padding: 4px; }
QFrame#section { background: #18212b; border: 1px solid #243142; border-radius: 4px; }
QFrame#sechead { background: #1c2733; border: none; border-top-left-radius: 4px; border-top-right-radius: 4px; }
QFrame#uvsettings { background: #141c25; border: 1px solid #243142; border-radius: 3px; }
QPushButton { background: #2a3645; color: #e0e8f0; border: 1px solid #3a4a5d;
              border-radius: 3px; padding: 3px 10px; min-height: 18px; }
QPushButton:hover { background: #364658; }
QPushButton:pressed { background: #202b38; }
QPushButton:disabled { background: #1b232d; color: #5b6673; border-color: #242e3a; }
QPushButton#runBtn { background: #2f3b4a; font-weight: bold; }
QPushButton#runBtn:hover { background: #3d4d60; }
QPushButton#resBtn { background: #232e3b; }
QPushButton#resBtn:checked { background: #1e90ff; border-color: #55adff; color: white; font-weight: bold; }
QPushButton#bottomBtn { background: #1f2a37; border: 1px solid #34465a; min-height: 20px; }
QPushButton#bottomBtn:hover { background: #2b3a4c; }
QPushButton#runAll { background: #1f9d5a; border: 1px solid #2bc274; font-weight: bold;
                     font-size: 13px; min-height: 28px; color: white; }
QPushButton#runAll:hover { background: #26b86a; }
QComboBox, QSpinBox, QDoubleSpinBox { background: #1b2530; color: #e6edf5; border: 1px solid #34465a;
                    border-radius: 3px; padding: 3px 6px; min-height: 20px; }
QComboBox QAbstractItemView { background: #1b2530; color: #e6edf5; selection-background-color: #2d8cff; }
QToolButton { background: #1b2530; border: 1px solid #34465a; border-radius: 3px; padding: 2px; }
QToolButton:hover { background: #2b3a4c; }
QToolButton::menu-indicator { image: none; }
QScrollArea { border: none; background: transparent; }
QScrollBar:vertical { background: #121820; width: 10px; margin: 0; }
QScrollBar::handle:vertical { background: #34465a; border-radius: 4px; min-height: 30px; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QMenu { background: #1b2530; color: #e6edf5; border: 1px solid #34465a; }
QMenu::item:selected { background: #2d8cff; }
"""


def _maya_main_window():
    ptr = omui.MQtUtil.mainWindow()
    if ptr is None:
        return None
    return wrapInstance(int(ptr), QtWidgets.QWidget)


# --------------------------------------------------------------------------
# Main window
# --------------------------------------------------------------------------
class QualityCheckUI(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super(QualityCheckUI, self).__init__(parent)
        self.setObjectName("MayaQualityCheckUI")
        self.setWindowTitle(TOOL_NAME)
        self.setWindowIcon(QtGui.QIcon(make_icon("logo", size=32)))
        self.setWindowFlags(QtCore.Qt.Window | QtCore.Qt.WindowMinMaxButtonsHint |
                            QtCore.Qt.WindowCloseButtonHint)
        self.setStyleSheet(STYLE)
        self.resize(640, 900)
        self.rows = []
        self.sections = {}
        self.last_scope = u""

        root = QtWidgets.QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(8)

        # --- top bar: scope + preset + gear + menu --------------------------
        top = QtWidgets.QHBoxLayout()
        top.setSpacing(6)
        left = QtWidgets.QVBoxLayout()
        left.setSpacing(1)
        self.scope_label = QtWidgets.QLabel()
        self.scope_label.setStyleSheet("color:#37a0ff; font-size:13px; font-weight:bold;")
        self.summary_label = QtWidgets.QLabel()
        left.addWidget(self.scope_label)
        left.addWidget(self.summary_label)
        top.addLayout(left, 1)

        preset_lbl = QtWidgets.QLabel("Preset:")
        preset_lbl.setStyleSheet("font-weight:bold;")
        self.preset_combo = QtWidgets.QComboBox()
        self.preset_combo.setMinimumWidth(190)
        for name, _off, _res in PRESETS:
            self.preset_combo.addItem(name)
        self.preset_combo.setToolTip("Presets switch checks on/off and set the UV padding values.")

        self.gear_btn = QtWidgets.QToolButton()
        self.gear_btn.setIcon(QtGui.QIcon(make_icon("gear", "#cfd8e3", 22)))
        self.gear_btn.setToolTip("Check settings (thresholds)")
        self.gear_btn.setFixedSize(30, 28)
        self.more_btn = QtWidgets.QToolButton()
        self.more_btn.setIcon(QtGui.QIcon(make_icon("dots", "#cfd8e3", 22)))
        self.more_btn.setFixedSize(30, 28)
        self.more_btn.setPopupMode(QtWidgets.QToolButton.InstantPopup)
        menu = QtWidgets.QMenu(self.more_btn)
        menu.addAction("Export Report...", self.export_report)
        menu.addAction("Refresh Scope", self.refresh_scope)
        menu.addAction("Reset All Results", self.reset_results)
        menu.addSeparator()
        menu.addAction("About", self.about)
        self.more_btn.setMenu(menu)

        top.addWidget(preset_lbl)
        top.addWidget(self.preset_combo)
        top.addWidget(self.gear_btn)
        top.addWidget(self.more_btn)
        root.addLayout(top)

        # --- scroll area with sections --------------------------------------
        scroll = QtWidgets.QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)
        holder = QtWidgets.QWidget()
        holder_lay = QtWidgets.QVBoxLayout(holder)
        holder_lay.setContentsMargins(0, 0, 6, 0)
        holder_lay.setSpacing(8)

        self.uv_settings = None
        for gid, title, color, icon in SECTIONS:
            section = SectionFrame(title, color, icon)
            if gid == "UVPAD":
                self.uv_settings = UVPaddingSettings(self._uv_settings_changed)
                section.body_layout.addWidget(self.uv_settings)
                section.body_layout.addSpacing(4)
            for check in [c for c in CHECKS if c[0] == gid]:
                row = CheckRow(check, self.run_one, self.select_errors)
                section.body_layout.addWidget(row)
                self.rows.append(row)
            holder_lay.addWidget(section)
            self.sections[gid] = section
        holder_lay.addStretch(1)
        scroll.setWidget(holder)
        root.addWidget(scroll, 1)

        # --- bottom buttons -------------------------------------------------
        btns = QtWidgets.QHBoxLayout()
        btns.setSpacing(6)
        for text, slot in (("Uncheck All", self.uncheck_all), ("Invert", self.invert),
                           ("Check Failed Only", self.check_failed_only),
                           ("Check All", self.check_all)):
            b = QtWidgets.QPushButton(text)
            b.setObjectName("bottomBtn")
            b.clicked.connect(slot)
            btns.addWidget(b, 1)
        root.addLayout(btns)

        run_all = QtWidgets.QPushButton(u"\u25B6   RUN ALL CHECKED")
        run_all.setObjectName("runAll")
        run_all.clicked.connect(self.run_checked)
        root.addWidget(run_all)

        credit = QtWidgets.QLabel(TOOL_NAME)
        credit.setAlignment(QtCore.Qt.AlignCenter)
        credit.setStyleSheet("color:#5f7288; font-size:10px;")
        root.addWidget(credit)

        self.preset_combo.currentIndexChanged.connect(self.apply_preset)
        self.gear_btn.clicked.connect(self.open_thresholds)

        self.apply_preset(0)
        self.refresh_scope()
        self.update_summary()

    # -- scope / summary -------------------------------------------------------
    def refresh_scope(self):
        scope = Scope()
        self.last_scope = scope.describe()
        self.scope_label.setText(self.last_scope)
        if getattr(self, "uv_settings", None) is not None:
            self.uv_settings.set_uv_sets(_scope_uv_sets(scope))

    def update_summary(self):
        passed = sum(1 for r in self.rows if r.state == "pass")
        failed = sum(1 for r in self.rows if r.state == "fail")
        idle = sum(1 for r in self.rows if r.state == "idle")
        self.summary_label.setText(
            u'<span style="color:#6fd68c">Passed %d</span> &nbsp;&middot;&nbsp; '
            u'<span style="color:#ff7a8a">Failed %d</span> &nbsp;&middot;&nbsp; '
            u'<span style="color:#93a3b5">Not run %d</span>' % (passed, failed, idle))

    def changeEvent(self, event):
        if event.type() == QtCore.QEvent.ActivationChange and self.isActiveWindow():
            self.refresh_scope()
        super(QualityCheckUI, self).changeEvent(event)

    # -- presets / settings ----------------------------------------------------
    def apply_preset(self, index):
        name, off, res = PRESETS[index]
        for r in self.rows:
            r.checkbox.setChecked(r.key not in off)
        if res:
            set_resolution(res[0])      # padding comes from PADDING_BY_RESOLUTION
            self.uv_settings.refresh_from_settings()
            self._uv_settings_changed()

    def _uv_settings_changed(self):
        for r in self.rows:
            if r.group == "UVPAD":
                r.reset()
        self.update_summary()

    def open_thresholds(self):
        dlg = ThresholdDialog(self)
        if dlg.exec_() if hasattr(dlg, "exec_") else dlg.exec():
            self.reset_results()

    def reset_results(self):
        for r in self.rows:
            r.reset()
        self.update_summary()

    def about(self):
        QtWidgets.QMessageBox.information(
            self, TOOL_NAME,
            u"%s\n\nModel quality checker for General, Naming, Modeling, Normals, "
            u"Topology, UVs and UV Padding.\nMinimum Maya version: 2017." % TOOL_NAME)

    # -- running -----------------------------------------------------------------
    def _run_row(self, row, scope):
        try:
            row.set_result(row.func(scope))
        except Exception:
            traceback.print_exc()
            row.set_exception(traceback.format_exc(limit=3))

    def run_one(self, row):
        scope = Scope()
        self.scope_label.setText(scope.describe())
        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.WaitCursor)
        try:
            self._run_row(row, scope)
        finally:
            QtWidgets.QApplication.restoreOverrideCursor()
        self.update_summary()

    def run_checked(self):
        scope = Scope()
        self.scope_label.setText(scope.describe())
        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.WaitCursor)
        try:
            for row in self.rows:
                if row.checkbox.isChecked():
                    self._run_row(row, scope)
                    self.update_summary()
                    QtWidgets.QApplication.processEvents()
        finally:
            QtWidgets.QApplication.restoreOverrideCursor()
        self.update_summary()

    def select_errors(self, row):
        if not row.errors:
            return
        if row.group == "UVPAD":
            _activate_uv_sets(row.errors)
        try:
            cmds.select(row.errors, replace=True)
        except Exception:
            cmds.warning("Some error nodes no longer exist. Run the check again.")
            return
        try:
            comps = [e for e in row.errors if "." in e and "[" in e]
            if comps:
                cmds.hilite(_uniq([e.split(".")[0] for e in comps]))
        except Exception:
            pass

    # -- checkbox helpers ------------------------------------------------------
    def check_all(self):
        for r in self.rows:
            r.checkbox.setChecked(True)

    def uncheck_all(self):
        for r in self.rows:
            r.checkbox.setChecked(False)

    def invert(self):
        for r in self.rows:
            r.checkbox.setChecked(not r.checkbox.isChecked())

    def check_failed_only(self):
        for r in self.rows:
            r.checkbox.setChecked(r.state == "fail")

    # -- report ------------------------------------------------------------------
    def export_report(self):
        res = QtWidgets.QFileDialog.getSaveFileName(
            self, "Export Report", os.path.expanduser("~/quality_report.txt"), "Text (*.txt)")
        path = res[0] if isinstance(res, (tuple, list)) else res
        if not path:
            return
        lines = [TOOL_NAME, datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
                 cmds.file(q=True, sceneName=True) or "(untitled scene)", self.last_scope, ""]
        titles = dict((g, t) for g, t, _c, _i in SECTIONS)
        for gid, _t, _c, _i in SECTIONS:
            lines.append("[%s]" % titles[gid])
            for r in [x for x in self.rows if x.group == gid]:
                tag = {"pass": "PASS", "fail": "FAIL", "idle": "----"}.get(r.state, "ERR ")
                count = " (%d)" % len(r.errors) if r.errors else ""
                lines.append("  %s  %s%s" % (tag, r.label_text, count))
                for e in (r.errors or [])[:200]:
                    lines.append("        %s" % e)
            lines.append("")
        try:
            with open(path, "w") as fh:
                fh.write(u"\n".join(lines).encode("utf-8") if sys.version_info[0] < 3
                         else u"\n".join(lines))
            cmds.inViewMessage(amg="Report saved", pos="midCenter", fade=True)
        except Exception as exc:
            cmds.warning("Could not save report: %s" % exc)


_WINDOW = None


def show():
    """Open the Maya Quality Check window (re-opens if already open)."""
    global _WINDOW
    for w in QtWidgets.QApplication.allWidgets():
        try:
            if w.objectName() == "MayaQualityCheckUI":
                w.close()
                w.deleteLater()
        except Exception:
            pass
    _WINDOW = QualityCheckUI(_maya_main_window())
    _WINDOW.show()
    return _WINDOW


# --------------------------------------------------------------------------
# Drag & drop installer
# --------------------------------------------------------------------------
SHELF_COMMAND = ("import %s as _mqc\ntry:\n    reload(_mqc)\nexcept NameError:\n"
                 "    import importlib\n    importlib.reload(_mqc)\n_mqc.show()" % MODULE_NAME)


def _add_shelf_button():
    try:
        top = mel.eval("$tmp = $gShelfTopLevel")
        current = cmds.tabLayout(top, q=True, selectTab=True)
        for b in cmds.shelfLayout(current, q=True, childArray=True) or []:
            try:
                if cmds.shelfButton(b, q=True, docTag=True) == "MQC_TOOL":
                    cmds.deleteUI(b)
            except Exception:
                pass
        cmds.shelfButton(parent=current, label=TOOL_NAME, annotation=TOOL_NAME,
                         docTag="MQC_TOOL", image1="commandButton.png",
                         imageOverlayLabel="MQC", overlayLabelColor=(1, 1, 1),
                         overlayLabelBackColor=(0.1, 0.55, 0.45, 0.9),
                         sourceType="python", command=SHELF_COMMAND)
        return True
    except Exception:
        traceback.print_exc()
        return False


def onMayaDroppedPythonFile(*args):
    """Called by Maya when this file is dragged into the viewport."""
    src = None
    for a in args:
        if isinstance(a, string_types) and a.lower().endswith(".py") and os.path.isfile(a):
            src = a
            break
    if src is None:
        src = globals().get("__file__")
    if not src:
        cmds.warning("%s: could not locate the dropped file." % TOOL_NAME)
        return

    src = os.path.splitext(src)[0] + ".py"
    try:
        if cmds.about(apiVersion=True) < MIN_API_VERSION:
            cmds.warning("%s needs Maya %d or newer; this version is not supported."
                         % (TOOL_NAME, MIN_MAYA_VERSION))
    except Exception:
        pass
    dest_dir = cmds.internalVar(userScriptDir=True)
    dest = os.path.join(dest_dir, MODULE_NAME + ".py")
    try:
        if not os.path.isdir(dest_dir):
            os.makedirs(dest_dir)
        if os.path.normcase(os.path.abspath(src)) != os.path.normcase(os.path.abspath(dest)):
            shutil.copyfile(src, dest)
    except (IOError, OSError):
        # scripts folder not writable: run straight from where the file was dropped
        dest_dir = os.path.dirname(os.path.abspath(src))
        if os.path.basename(src) != MODULE_NAME + ".py":
            cmds.warning("%s: could not copy to the scripts folder; rename the file to %s.py "
                         "and drop it again." % (TOOL_NAME, MODULE_NAME))
            return
    if dest_dir not in sys.path:
        sys.path.append(dest_dir)

    try:
        import importlib
        if MODULE_NAME in sys.modules:
            try:
                from importlib import reload as _reload
            except ImportError:
                _reload = reload  # noqa: F821  (Python 2)
            mod = _reload(sys.modules[MODULE_NAME])
        else:
            mod = importlib.import_module(MODULE_NAME)
    except Exception:
        traceback.print_exc()
        cmds.warning("%s: install failed, see Script Editor." % TOOL_NAME)
        return

    added = _add_shelf_button()
    mod.show()
    print("// %s installed%s" % (TOOL_NAME, " (shelf button added)" if added else ""))
    cmds.inViewMessage(
        amg="<hl>%s</hl> installed%s" % (TOOL_NAME, " - shelf button added" if added else ""),
        pos="midCenter", fade=True)


if __name__ == "__main__":
    show()
