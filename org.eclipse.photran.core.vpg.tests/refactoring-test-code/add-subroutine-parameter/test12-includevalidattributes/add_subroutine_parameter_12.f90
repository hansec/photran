program validattributes ! Tests that valid attributes (intent(inout)) are allowed.

end program validattributes
subroutine sub(z) !<<<<< 4, 1, 4, 5, integer; intent(inout) :: y, 0, 0, pass
    integer, intent(in) :: z
end subroutine
