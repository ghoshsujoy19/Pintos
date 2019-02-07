#define f (1 << 14)
#define INT_MAX ((1 << 31) - 1)
#define INT_MIN (-(1 << 31))

static int 
int_to_fixedpt (int n)
{
  return n * f;
}

static int 
fixedpt_to_int (int x)
{
  return x / f;
}

static int 
fixedpt_to_int_round_near (int x)
{
  if (x >= 0)
    return (x + f / 2) / f;
  else	
    return (x - f / 2) / f;
}

static int 
add_float_float(int x, int y)
{
  return x + y;
}

static int 
add_float_int (int x, int n)
{
  return x + n * f;	
}

static int 
sub_float_float (int x, int y)
{
  return x - y;
}

static int 
sub_float_int (int x, int n)
{
  return x - n * f; 
}

static int 
sub_int_float (int n, int x)
{
  return n * f - x; 
}

static int 
mul_float_float (int x, int y)
{
  return ((int64_t)x) * y / f;
}

static int 
mul_float_int (int x, int y)
{
  return x * y;
}

static int 
div_float_float (int x, int y)
{
  return ((int64_t)x) * f / y;	
}

static int 
div_float_int (int x, int y)
{
  return x / y;
}

