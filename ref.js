function toggle_mir(cb) {
    var mir = cb.parentNode.parentNode.querySelector(".mir");
    mir.style.display = cb.checked ? 'flex' : 'none';
}
