sed -i -e 's/pub struct rosidl_message_type_support_t/struct rosidl_message_type_support_t_/' \
-e 's/pub struct rosidl_service_type_support_t/struct rosidl_service_type_support_t_/' \
-e 's/"\* */"a /' \
-e '1iuse crate::rcl::{rosidl_message_type_support_t, rosidl_service_type_support_t};' $1
