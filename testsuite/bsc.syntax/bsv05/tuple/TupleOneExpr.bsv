// tuple(e) is e; later argument lists apply that value

function Bool f() = tuple(True);
function Bool inv(Bool b) = !b;
function Bool direct() = tuple(inv)(True);
function Bool parenthesized() = (tuple(inv))(True);
