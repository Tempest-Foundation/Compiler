import "private_var_a.sl";
import "private_var_b.sl";

#[export]
pub fn optimized_var_sum() i32 {
	return private_var_a_value() + private_var_b_value();
}

#[export]
pub fn optimized_var_a_address() *mut i32 {
	return private_var_a_address();
}

#[export]
pub fn optimized_var_b_address() *mut i32 {
	return private_var_b_address();
}