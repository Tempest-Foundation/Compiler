let mut SHARED_STATE: i32 = 23;

#[export]
pub fn private_var_b_value() i32 {
	return SHARED_STATE;
}

#[export]
pub fn private_var_b_address() *mut i32 {
	return &SHARED_STATE;
}