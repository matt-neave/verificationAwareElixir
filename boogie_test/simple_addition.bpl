procedure add(x: int, y: int) returns (z: int)
    requires x > 0;
    ensures z == x + y;
{
    if (x < 0) 
    {
        z := x * z;
    } else {
        z := x + y;
    }
}

procedure square(x: int) returns (z: int)
    ensures z >= 0;
    ensures z == x * x;
{
    z := x * x;
}

procedure area_of_square(x: int) returns (z: int)
    ensures z >= 0;
{
    call z := square(x);
}

procedure area_of_square_2(x: int) returns (z: int)
    ensures z >= 0;
{
    call z := add(x, x);
    call z := add(z, z);
}