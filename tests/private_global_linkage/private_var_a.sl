let mut SHARED_STATE: i32 = 13;

#[export]
pub fn private_var_a_value() i32 {
	return SHARED_STATE;
}

#[export]
pub fn private_var_a_address() *mut i32 {
	return &SHARED_STATE;
}