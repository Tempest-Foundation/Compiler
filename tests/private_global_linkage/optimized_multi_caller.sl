import "private_a.sl";
import "private_b.sl";

#[export]
pub fn optimized_multi_caller() i32 {
	return private_a_value() + private_b_value();
}