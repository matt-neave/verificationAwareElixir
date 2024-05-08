#define data_t byte

typedef data_record {
  data_t me;
  bool allocated;
  // .... your data fields here ....
}

#define NUMBER_OF_DATA_RECORDS 10

data_record data_record_array[NUMBER_OF_DATA_RECORDS];

#define DATA_RECORD_ALLOCATED(idx)    data_record_array[(idx)].allocated
#define DATA_RECORD_ME(idx)           data_record_array[(idx)].me

// Assigns data_ptr with a free data_record index
inline data_record_allocate (data_t data_ptr)
{
data_ptr = 0; 
do
:: data_itr >= NUMBER_OF_DATA_RECORDS -> break
:: else ->
        if
        :: ! DATA_RECORD_ALLOCATED (data_itr) -> 
        DATA_RECORD_ALLOCATED (data_itr) = true
        DATA_RECORD_ME (data_itr) = data_it
        break
        :: else -> data_itr++
        fi
od
}
inline data_record_free (data_t data_ptr)
{
    DATA_RECORD_ALLOCATED (data_itr) = false
    data_itr = NUMBER_OF_DATA_RECORDS
}


init {
    printf("Hi\n");
}