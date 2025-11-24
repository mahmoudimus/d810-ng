# cython: language_level=3, embedsignature=True
# distutils: language=c++
# distutils: define_macros=__EA64__=1

from libc.stdint cimport uintptr_t
from libc.stddef cimport size_t
from libcpp.pair cimport pair
from libcpp.map cimport map
from libcpp.unordered_map cimport unordered_map
from libcpp.memory cimport shared_ptr
from cpython cimport PyObject, PyObject_GetAttrString
from cython.operator cimport dereference as deref

# cython does not wrap stdarg
cdef extern from "stdarg.h":
    ctypedef struct va_list:
        pass

cdef extern from "swigpyobject.h":
    ctypedef struct SwigPyObject:
        void *ptr

    T swigtocpp[T](PyObject *obj)

ctypedef SwigPyObject* SwigPyObjectPtr

cdef inline void* _swig_ptr(object obj):
    addr = PyObject_GetAttrString(obj, "this")
    # Return the actual C++ pointer (s.ptr) stored in the SwigPyObject
    return (<SwigPyObjectPtr>addr).ptr


cdef extern from "pro.h":
    ctypedef unsigned char uchar   # unsigned 8 bit value/
    ctypedef unsigned short ushort  # unsigned 16 bit value
    ctypedef unsigned int uint    # unsigned 32 bit value
    ctypedef unsigned char uint8 # unsigned 8 bit value
    ctypedef          char int8 # signed 8 bit value
    ctypedef unsigned short uint16 # unsigned 16 bit value
    ctypedef          short int16 # signed 16 bit value
    ctypedef unsigned int uint32 # unsigned 32 bit value
    ctypedef          int int32 # signed 32 bit value
    ctypedef unsigned long long uint64 # unsigned 64 bit value
    ctypedef          long long int64 # signed 64 bit value

    ctypedef uint64 ea_t
    ctypedef uint64 sel_t
    ctypedef uint64 asize_t
    ctypedef int64 adiff_t

    ctypedef asize_t uval_t   # unsigned value used by the processor.
                              #  - for 32-bit ::ea_t - ::uint32
                              #  - for 64-bit ::ea_t - ::uint64
    ctypedef adiff_t sval_t   # signed value used by the processor.
                              #  - for 32-bit ::ea_t - ::int32
                              #  - for 64-bit ::ea_t - ::int64

    ctypedef uint32 ea32_t    # 32-bit address, regardless of IDA bitness.
                              # this type can be used when we know in advance
                              # that 32 bits are enough to hold an address.
    ctypedef uint64 ea64_t    # 64-bit address, regardless of IDA bitness.
                              # we need this type for interoperability with
                              # debug servers, lumina, etc

    # Error code (errno)
    ctypedef int error_t

    ctypedef uint8 op_dtype_t

    # The inode_t type is the specialization specific inode number.
    # For example, it can represent a local type ordinal or a structure id.
    ctypedef uval_t inode_t

    # A position in the difference source.
    # This is an abstract value that depends on the difference source.
    # It should be something that can be used to conveniently retrieve information
    # from a difference source. For example, for the name list it can be the index
    # in the name list. For structure view it can be the position in the list of structs.
    # Please note that this is not necessarily an address. However, for the purpose
    # of comparing the contents of the disassembly listing it can be an address.
    #
    # diffpos_t instances must have the following property: adding or removing
    # items to diff_source_t should not invalidate the existing diffpos_t instances.
    # They must stay valid after adding or removing items to diff_source_t.
    # Naturally, deleting an item pointed by diffpos_t may render it incorrect,
    # this is acceptable and expected.
    ctypedef size_t diffpos_t


    cdef cppclass qvector[T]:
        ctypedef T value_type  # the type of objects contained in this qvector

        # Constructor
        qvector() except +
        # Constructor - creates a new qvector identical to 'x'
        qvector_from_copy "qvector"(const qvector[T]& x) except +

        # Move constructor (not supported in Cython, emulate with copy constructor)
        # Cython does not support rvalue references; use the copy constructor instead.
        # Users should be aware this will copy, not move.
        # qvector_from_move "qvector"(qvector[T]&& x) except +

        # Append a new element to the end the qvector.
        void push_back(const T& x) except +
        # Append a new element to the end the qvector with a move semantics.
        # Requires a fix for IDA Pro's `pro.h` header.
        # /// Append a new element to the end the qvector with a move semantics.
        # void push_back(T &&x)
        # {
        # #ifdef TESTABLE_BUILD
        #     QASSERT(1977, !ref_within_range(x));
        # #endif
        #     reserve(n+1);
        #     // FIX: IDA has a bug here.
        #     // - new (array+n) T(x);  <--- bug
        #     // + new (array+n) T(std::move(x));  <--- fix
        #     new (array+n) T(std::move(x));
        #     ++n;
        # }
        void push_back_move "push_back"(T&& x) except +
        # Append a new empty element to the end of the qvector.
        # \return a reference to this new element
        T& push_back_and_get_ref "push_back"(const T& x) except +

        # Remove the last element in the qvector
        void pop_back() except +

        # Get the number of elements in the qvector
        size_t size() const
        # Does the qvector have 0 elements?
        bint empty() const

        # Allows use of typical c-style array indexing for qvectors (const)
        const T& const_op_getitem "operator[]"(size_t _idx) const
        # Allows use of typical c-style array indexing for qvectors
        T& operator[](size_t _idx)

        # Get element at index '_idx' (const)
        const T& const_at "at"(size_t _idx) const
        # Get element at index '_idx'
        T& at(size_t _idx)

        # Get the first element in the qvector (const)
        const T& const_front "front"() const
        # Get the first element in the qvector
        T& front()

        # Get the last element in the qvector (const)
        const T& const_back "back"() const
        # Get the last element in the qvector
        T& back()

        # Destroy all elements but do not free memory
        void qclear() except +
        # Destroy all elements and free memory
        void clear() except +

        # Allow assignment of one qvector to another using '='
        qvector[T]& assign_from_copy "operator="(const qvector[T]& x) except +
        # Move assignment operator (not supported in Cython, emulate with copy constructor)
        # Cython does not support rvalue references; use the copy constructor instead.
        # Users should be aware this will copy, not move.
        # qvector[T]& assign_from_move "operator="(qvector[T]&& x) except +

        # Resize to the given size.
        # If the given size (_newsize) is less than the current size (n) of the qvector, then the last n - _newsize elements are simply deleted.
        # If the given size is greater than the current size, the qvector is grown to _newsize, and the last _newsize - n elements will be filled with copies of 'x'.
        # If the given size is equal to the current size, this function does nothing.
        void resize(size_t _newsize, const T& x) except +
        # Same as resize(size_t, const T &), but extra space is filled with empty elements
        void resize_with_default "resize"(size_t _newsize) except +
        # Resize the array but do not initialize elements
        void resize_noinit(size_t _newsize) except +

        # Add an element to the end of the qvector, which will be a new T() if x is not given
        void grow(const T& x) except +

        # Get the number of elements that this qvector can contain - not the same
        # as the number of elements currently in the qvector (size())
        size_t capacity() const
        # Increase the capacity of the qvector. If cnt is not greater than the current capacity
        # this function does nothing.
        void reserve(size_t cnt) except +

        # Shrink the capacity down to the current number of elements
        void truncate() except +

        # Replace all attributes of this qvector with that of 'r', and vice versa.
        # Effectively sets this = r and r = this without copying/allocating any memory.
        void swap(qvector[T]& r) except +

        # Empty the qvector and return a pointer to it's contents.
        # The caller must free the result of this function
        T* extract() except +
        # Populate the qvector with dynamic memory.
        # The qvector must be empty before calling this method!
        void inject(T* s, size_t len) except +

        # Allow ability to test the equality of two qvectors using '=='
        bint operator==(const qvector[T]& r) const
        # Allow ability to test equality of two qvectors using '!='
        bint operator!=(const qvector[T]& r) const

        ctypedef T* iterator
        ctypedef const T* const_iterator

        # Get an iterator that points to the first element in the qvector
        iterator begin()
        # Get a const iterator that points to the first element in the qvector
        const_iterator const_begin "begin"() const
        # Get an iterator that points to the end of the qvector (NOT the last element)
        iterator end()
        # Get a const iterator that points to the end of the qvector (NOT the last element)
        const_iterator const_end "end"() const

        # Insert an element into the qvector at a specified position.
        # \param it  an iterator that points to the desired position of the new element
        # \param x  the element to insert
        # \return an iterator that points to the newly inserted element
        iterator insert_copy "insert"(iterator it, const T& x) except +
        # Insert an element into the qvector with a move semantics.
        iterator insert_move "insert"(iterator it, T&& x) except +
        # # Insert a several elements to the qvector at a specified position.
        # # \param it     position at which new elements will be inserted
        # # \param first  pointer to first element to be inserted
        # # \param last   pointer to end of elements to be inserted (the element pointed to by 'last' will not be included)
        # # \return an iterator that points to the first newly inserted element.
        # iterator insert_range "insert"(iterator it, it2 first, it2 last) except +

        # Remove an element from the qvector.
        # \param it  pointer to element to be removed
        # \return pointer to the element that took its place
        iterator erase_at "erase"(iterator it) except +
        # Remove a subset of the qvector.
        # \param first  pointer to head of subset to be removed
        # \param last   pointer to end of subset to be removed (element pointed to by last will not be removed)
        # \return a pointer to the element that took the place of 'first'
        iterator erase_range "erase"(iterator first, iterator last) except +

        # Find an element in the qvector.
        # \param x  element to find
        # \return an iterator that points to the first occurrence of 'x'
        iterator find(const T& x)
        # \copydoc find (const version)
        const_iterator const_find "find"(const T& x) const

        # Find index of the specified value or return -1
        ssize_t index(const T& x) const

        # Add an element to the end of the qvector
        void add(const T& x) except +
        # Add an element to the end of the qvector (move version)
        void add_move "add"(T&& x) except +

        # Does the qvector contain x?
        bint has(const T& x) const
        # Add an element to the end of the qvector - only if it isn't already present.
        # \param x  the element to add
        # \return false if 'x' is already in the qvector, true otherwise
        bint add_unique(const T& x) except +

        # Find an element and remove it.
        # \param x  the element to remove
        # \return false if 'x' was not found, true otherwise
        bint delete "del"(const T& x) except +

        # debug print
        const char* dstr() const

    cdef cppclass _qstring[T]:

        # Constructor
        _qstring() except +
        # Constructor - creates a new qstring from an existing char *
        _qstring(const T *ptr) except +
        # Constructor - creates a new qstring using first 'len' chars from 'ptr'
        _qstring(const T *ptr, size_t len) except +
        # Constructor - constructs the string with 'count' copies of character 'ch'
        _qstring(size_t count, T ch) except +

        # Swap contents of two qstrings. see qvector::swap()
        void swap(_qstring[T] &r) except +
        # Get number of chars in this qstring (not including terminating zero)
        size_t length() const
        # Get number of chars in this qstring (including terminating zero)
        size_t size() const
        # Get number of chars this qstring can contain (including terminating zero)
        size_t capacity() const

        # Resize to the given size.
        # The resulting qstring will have length() = s, and size() = s+1
        # if 's' is greater than the current size then the extra space is filled with 'c'.
        # if 's' is less than the current size then the trailing chars are removed
        void resize(size_t s, T c) except +
        # Similar to resize(size_t, qchar) - but any extra space is filled with zeroes
        void resize_no_fill "resize"(size_t s) except +
        void remove_last(int cnt=1) except +
        # Increase capacity the qstring. see qvector::reserve()
        void reserve(size_t cnt) except +
        # Clear qstring and free memory
        void clear() except +
        # Clear qstring but do not free memory yet
        void qclear() except +
        # Does the qstring have 0 non-null elements?
        bint empty() const
        # Convert the qstring to a char *
        const T *c_str() const

        ctypedef T *iterator
        ctypedef const T *const_iterator
        # Get a pointer to the beginning of the qstring
        iterator begin()
        # Get a const pointer to the beginning of the qstring
        const_iterator const_begin "begin"() const
        # Get a pointer to the end of the qstring (this is not the terminating zero)
        iterator end()
        # Get a const pointer to the end of the qstring (this is not the terminating zero)
        const_iterator const_end "end"() const

        # Allow assignment of qstrings using '='
        _qstring[T]& operator=(const T *str) except +
        _qstring[T]& assign_from_qstring "operator="(const _qstring[T] &qstr) except +

        # Append a char using '+='
        _qstring[T]& operator_iadd_char "operator+="(T c) except +
        # Append another qstring using '+='
        _qstring[T]& operator_iadd_qstring "operator+="(const _qstring[T] &r) except +
        # Get result of appending two qstrings using '+'
        _qstring[T] operator+(const _qstring[T] &r) const

        bint operator==(const _qstring[T]& r) const
        bint operator!=(const _qstring[T]& r) const
        bint operator<(const _qstring[T]& r) const
        bint operator>(const _qstring[T]& r) const
        bint operator<=(const _qstring[T]& r) const
        bint operator>=(const _qstring[T]& r) const

        # Test equality of a qstring and a const char* using '=='
        bint operator_eq_ptr "operator=="(const T *r) const
        # Test equality of a qstring and a const char* with '!='
        bint operator_ne_ptr "operator!=" (const T *r) const
        # Compare two qstrings using '<'. see qstrcmp()
        bint operator_lt_ptr "operator<"(const T *r) const

        # Does the string start with the specified prefix?
        bint starts_with_qstring "starts_with"(const _qstring[T] &str) const
        bint starts_with_ptr "starts_with"(const T *ptr, ssize_t len) const
        # Does the string end with the specified suffix?
        bint ends_with_qstring "ends_with"(const _qstring[T] &str) const
        bint ends_with_ptr "ends_with"(const T *ptr, ssize_t len) const

        # Retrieve char at index 'idx' using '[]'
        const T& const_op_getitem "operator[]"(size_t idx) const
        # Retrieve char at index 'idx' using '[]'
        T& operator[](size_t idx)

        # Retrieve const char at index 'idx'
        const T& const_at "at"(size_t idx) const
        # Retrieve char at index 'idx'
        T& at(size_t idx) except +

        # Extract C string from _qstring. Must qfree() it.
        T *extract() except +
        # Assign this qstring to an existing char *.
        # See qvector::inject(T *, size_t)
        void inject(T *s, size_t len) except +
        # Same as to inject(qchar *, size_t), with len = strlen(s)
        void inject_ptr "inject"(T *s) except +
        # Get the last qchar in the string (for concatenation checks)
        T last() const

        # Find a substring.
        # \param str  the substring to look for
        # \param pos  starting position
        # \return the position of the beginning of the first occurrence of str, _qstring::npos of none exists
        size_t find_ptr "find"(const T *str, size_t pos=0) const
        # Same as find(const qchar *, size_t), but takes a qstring parameter
        size_t find_qstring "find"(const _qstring[T] &str, size_t pos=0) const
        # Find a character in the qstring.
        # \param c    the character to look for
        # \param pos  starting position
        # \return index of first occurrence of 'c' if c is found, _qstring::npos otherwise
        size_t find_char "find"(T c, size_t pos=0) const

        # Replace all occurrences of 'what' with 'with_this'.
        # \return false if 'what' is not found in the qstring, true otherwise
        bint replace(const T *what, const T *with_this) except +

        # Search backwards for a character in the qstring.
        # \param c    the char to look for
        # \param pos  starting position
        # \return index of first occurrence of 'c' if c is found, _qstring::npos otherwise
        size_t rfind(T c, size_t pos=0) const

        # Get a substring.
        # \param pos   starting position
        # \param n     ending position (non-inclusive)
        # \return the resulting substring
        _qstring[T] substr(size_t pos, size_t n) const

        # Remove characters from the qstring.
        # \param idx  starting position
        # \param cnt  number of characters to remove
        _qstring[T]& remove(size_t idx, size_t cnt) except +

        # Insert a character into the qstring.
        # \param idx  position of insertion (if idx >= length(), the effect is the same as append)
        # \param c    char to insert
        _qstring[T]& insert_char_at "insert"(size_t idx, T c) except +
        # Insert a string into the qstring.
        # \param idx     position of insertion (if idx >= length(), the effect is the same as append)
        # \param str     the string to insert
        # \param addlen  number of chars from 'str' to insert
        _qstring[T]& insert_substring_at "insert"(size_t idx, const T *str, size_t addlen) except +
        # Same as insert(size_t, const qchar *, size_t), but all chars in str are inserted
        _qstring[T]& insert_string_at "insert"(size_t idx, const T *str) except +
        # Same as insert(size_t, const qchar *), but takes a qstring parameter
        _qstring[T]& insert_qstring_at "insert"(size_t idx, const _qstring[T] &qstr) except +
        # Prepend the qstring with 'c'
        _qstring[T]& insert_char "insert"(T c) except +
        # Prepend the qstring with 'str'
        _qstring[T]& insert_string "insert"(const T *str) except +
        # Prepend the qstring with 'qstr'
        _qstring[T]& insert_qstring "insert"(const _qstring[T] &qstr) except +

        # Append c to the end of the qstring
        _qstring[T]& append(T c) except +
        # Append a string to the qstring.
        # \param str     the string to append
        # \param addlen  number of characters from 'str' to append
        _qstring[T]& append_substring "append"(const T *str, size_t addlen) except +
        # Same as append(const qchar *, size_t), but all chars in 'str' are appended
        _qstring[T]& append_string "append"(const T *str) except +
        # Same as append(const qchar *), but takes a qstring argument
        _qstring[T]& append_qstring "append"(const _qstring[T] &qstr) except +

        # Append result of qvsnprintf() to qstring
        _qstring[T]& cat_vsprnt(const char *format, ...) except +
        # Replace qstring with the result of qvsnprintf()
        _qstring[T]& vsprnt(const char *format, ...) except +
        # Append result of qsnprintf() to qstring
        _qstring[T]& cat_sprnt(const char *format, ...) except +
        # Replace qstring with the result of qsnprintf()
        _qstring[T]& sprnt(const char *format, ...) except +
        # Replace qstring with the result of qsnprintf()
        # \sa inline int nowarn_qsnprintf(char *buf, size_t size, const char *format, ...)
        _qstring[T]& nowarn_sprnt(const char *format, ...) except +

        # Fill qstring with a character.
        # The qstring is resized if necessary until 'len' chars have been filled
        # \param pos  starting position
        # \param c    the character to fill
        # \param len  number of positions to fill with 'c'
        _qstring[T]& fill(size_t pos, T c, size_t len) except +
        # Clear contents of qstring and fill with 'c'
        _qstring[T]& fill_all "fill"(T c, size_t len) except +

        # Remove all instances of the specified char from the beginning of the qstring
        _qstring[T]& ltrim(T blank) except +
        # Remove all instances of the specified char from the end of the qstring
        _qstring[T]& rtrim(T blank, size_t minlen = 0) except +
        # Remove all whitespace from the end of the qstring
        _qstring[T]& rtrim_whitespace "rtrim"() except +
        # Remove all instances of the specified char from both ends of the qstring
        _qstring[T]& trim2(T blank) except +


    # Vector of bytes (use for dynamic memory)
    cdef cppclass bytevec_t(qvector[uchar]):
        pass

    # instantiate for int
    ctypedef _qstring[char] qstring
    ctypedef qvector[qstring] qstringvec_t
    ctypedef qvector[uval_t] uvalvec_t    #< vector of unsigned values
    ctypedef qvector[sval_t] svalvec_t    #< vector of signed values
    ctypedef qvector[ea_t] eavec_t        #< vector of addresses
    ctypedef qvector[int] intvec_t        #< vector of integers
    ctypedef qvector[bint] boolvec_t      #< vector of bools
    ctypedef qvector[size_t] sizevec_t    #< vector of sizes
    int qsnprintf(char *str, size_t n, const char *fmt, ...)

    # cdef cppclass _qstring[T]:
    #     # Split a string on SEP, appending the parts to OUT
    #     # \param out storage
    #     # \param sep the separator to split on
    #     # \param flags a combination of \ref qstring_split_flags
    #     void split(qstringvec_t *out, const T *sep, uint32 flags) const
    #     # Join the provided parts into a single string with each element
    #     # separated by SEP
    #     # \param parts the parts to join
    #     # \param sep the separator to join on (it can be an empty string)
    #     # \return the combined string
    #     @staticmethod
    #     _qstring[T] join(const qstringvec_t &parts, const T *sep)


cdef extern from "ieee.h":
    cdef int FPVAL_NWORDS = 8  # number of words in fpvalue_t
    cdef cppclass fpvalue_t:
        ctypedef uint16[8] w

cdef extern from "ida.hpp":
    ctypedef uchar cm_t

cdef extern from "nalt.hpp":
    ctypedef uchar type_t;
    ctypedef uchar reftype_t;  # see \ref reftype_
    #-------------------------------------------------------------------------
    # \name Array representation
    #@{
    # Describes how to display an array
    cdef cppclass array_parameters_t:
        int32 flags
        # AP_ALLOWDUPS    0x00000001      # use 'dup' construct
        # AP_SIGNED       0x00000002      # treats numbers as signed
        # AP_INDEX        0x00000004      # display array element indexes as comments
        # AP_ARRAY        0x00000008      # create as array (this flag is not stored in database)
        # AP_IDXBASEMASK  0x000000F0      # mask for number base of the indexes
        #   AP_IDXDEC     0x00000000      # display indexes in decimal
        #   AP_IDXHEX     0x00000010      # display indexes in hex
        #   AP_IDXOCT     0x00000020      # display indexes in octal
        #   AP_IDXBIN     0x00000030      # display indexes in binary

        int32 lineitems        # number of items on a line
        int32 alignment        # -1 - don't align.
                               # 0  - align automatically.
                               # else item width

        # Constructor
        array_parameters_t(int32 _f, int32 _l, int32 _a)
        # Returns true if the parameters are default
        bint is_default() const


    # Information about a reference
    cdef cppclass refinfo_t:
        ea_t target      # reference target (#BADADDR-none)
        ea_t base        # base of reference (may be BADADDR)
        adiff_t tdelta   # offset from the target
        uint32 flags     # \ref REFINFO_

        # \defgroup REFINFO_ Reference info flags
        # Used by refinfo_t::flags
        #@{
        #define REFINFO_TYPE      0x000F  # reference type (reftype_t), or custom
                                          # reference ID if REFINFO_CUSTOM set
        #define REFINFO_RVAOFF    0x0010  # based reference (rva);
                                          # refinfo_t::base will be forced to get_imagebase();
                                          # such a reference is displayed with the \ash{a_rva} keyword
        #define REFINFO_PASTEND   0x0020  # reference past an item;
                                          # it may point to an nonexistent address;
                                          # do not destroy alignment dirs
        #define REFINFO_CUSTOM    0x0040  # a custom reference.
                                          # see custom_refinfo_handler_t.
                                          # the id of the custom refinfo is
                                          # stored under the REFINFO_TYPE mask.
        #define REFINFO_NOBASE    0x0080  # don't create the base xref;
                                          # implies that the base can be any value.
                                          # nb: base xrefs are created only if the offset base
                                          # points to the middle of a segment
        #define REFINFO_SUBTRACT  0x0100  # the reference value is subtracted from the base value instead of (as usual) being added to it
        #define REFINFO_SIGNEDOP  0x0200  # the operand value is sign-extended (only supported for REF_OFF8/16/32/64)
        #define REFINFO_NO_ZEROS  0x0400  # an opval of 0 will be considered invalid
        #define REFINFO_NO_ONES   0x0800  # an opval of ~0 will be considered invalid
        #define REFINFO_SELFREF   0x1000  # the self-based reference;
                                          # refinfo_t::base will be forced to the reference address
        #@}

        reftype_t type() const
        # \ref is_reftype_target_optional()
        bint is_target_optional() const
        bint no_base_xref() const
        bint is_pastend() const
        bint is_rvaoff() const
        bint is_custom() const
        bint is_subtract() const
        bint is_signed() const
        bint is_no_zeros() const
        bint is_no_ones() const
        bint is_selfref() const

        # RT can include REFINFO_CUSTOM bit
        void set_type(reftype_t rt)

        # init the structure with some default values
        # reft_and_flags should be REF_xxx optionally ORed with some REFINFO_xxx flags
        void init(uint32 reft_and_flags, ea_t _base, ea_t _target, adiff_t _tdelta)

        # internal use
        bint _require_base() const

cdef extern from "typeinf.hpp":
    ctypedef uint64 typid_t

    # Extended type attributes.
    # One-symbol keys are reserved to be used by the kernel.
    # The ones starting with an underscore are reserved too.
    cdef cppclass type_attr_t:
        qstring key      # one symbol keys are reserved to be used by the kernel
                         # the ones starting with an underscore are reserved too
        bytevec_t value  # attribute bytes

    # This vector must be sorted by keys
    ctypedef qvector[type_attr_t] type_attrs_t

    ctypedef int argloc_type_t
    cdef cppclass tinfo_t:
        typid_t typid


    # A high level variant of custom_data_type_ids_t
    cdef struct custom_data_type_info_t:
        int16 dtid    # data type id
        int16 fid     # data format ids

    # Visual representation of a member of a complex type (struct/union/enum)
    cdef cppclass value_repr_t:
        uint64 bits

        # Mask for the value type (* means requires additional info):
        # FRB_MASK   0xF
        # FRB_UNK    0x0     #   Unknown
        # FRB_NUMB   0x1     #   Binary number
        # FRB_NUMO   0x2     #   Octal number
        # FRB_NUMH   0x3     #   Hexadecimal number
        # FRB_NUMD   0x4     #   Decimal number
        # FRB_FLOAT  0x5     #   Floating point number (for interpreting an integer type as a floating value)
        # FRB_CHAR   0x6     #   Char
        # FRB_SEG    0x7     #   Segment
        # FRB_ENUM   0x8     #   *Enumeration
        # FRB_OFFSET 0x9     #   *Offset
        # FRB_STRLIT 0xA     #   *String literal (used for arrays)
        # FRB_STROFF 0xB     #   *Struct offset
        # FRB_CUSTOM 0xC     #   *Custom data type
        # FRB_INVSIGN  0x0100 # Invert sign (0x01 is represented as -0xFF)
        # FRB_INVBITS  0x0200 # Invert bits (0x01 is represented as ~0xFE)
        # FRB_SIGNED   0x0400 # Force signed representation
        # FRB_LZERO    0x0800 # Toggle leading zeroes (used for integers)
        # FRB_TABFORM  0x1000 # has additional tabular parameters

        # Additional info
        refinfo_t ri      # FRB_OFFSET
        int32 strtype     # FRB_STRLIT
        adiff_t delta     # FRB_STROFF
        uint32 type_ordinal # FRB_STROFF, FRB_ENUM
        custom_data_type_info_t cd # FRB_CUSTOM

        array_parameters_t ap # FRB_TABFORM, AP_SIGNED is ignored, use FRB_SIGNED instead

        # Swap with another value_repr_t
        void swap(value_repr_t &r)

        # Clear the value_repr_t (bits = 0)
        void clear()

        # Returns True if empty (bits == 0)
        bint empty() const

        # Returns True if enum ((bits & FRB_MASK) == FRB_ENUM)
        bint is_enum() const

        # Returns True if offset ((bits & FRB_MASK) == FRB_OFFSET)
        bint is_offset() const

        # Returns True if strlit ((bits & FRB_MASK) == FRB_STRLIT)
        bint is_strlit() const

        # Returns True if custom ((bits & FRB_MASK) == FRB_CUSTOM)
        bint is_custom() const

        # Returns True if stroff ((bits & FRB_MASK) == FRB_STROFF)
        bint is_stroff() const

        # Returns True if enum or stroff
        bint is_typref() const

        # Returns True if signed ((bits & FRB_SIGNED) != 0)
        bint is_signed() const

        # Returns True if has tabular form ((bits & FRB_TABFORM) != 0)
        bint has_tabform() const

        # Returns True if has leading zeroes ((bits & FRB_LZERO) != 0)
        bint has_lzeroes() const

        # Get value type (bits & FRB_MASK)
        uint64 get_vtype() const

        # Set value type
        void set_vtype(uint64 vt)

        # Set signed flag
        void set_signed(bint on)

        # Set tabular form flag
        void set_tabform(bint on)

        # Set leading zeroes flag
        void set_lzeroes(bint on)

        # Set array parameters
        void set_ap(const array_parameters_t &_ap)

        # Initialize array parameters
        void init_ap(array_parameters_t *_ap) const

        # Populate from opinfo
        # bint from_opinfo(flags64_t flags, aflags_t afl, const opinfo_t *opinfo, const array_parameters_t *_ap)

        # Print to qstring, optionally colored
        size_t print(qstring *result, bint colored) const

        # Parse value representation from string
        bint parse_value_repr(const qstring &attr, type_t target_type)

    #-------------------------------------------------------------------------
    # An object to represent struct or union members
    cdef cppclass udm_t:
        uint64 offset      # member offset in bits
        uint64 size        # size in bits
        qstring name       # member name
        qstring cmt        # member comment
        tinfo_t type       # member type
        value_repr_t repr  # radix, refinfo, strpath, custom_id, strtype
        int effalign       # effective field alignment (in bytes)
        uint32 tafld_bits  # TAH bits
        uchar fda          # field alignment (shift amount)

        udm_t() except +
        # # Create a structure/union member, with the specified name and arbitrary type.
        # #
        # # The 'size' will be set automatically.
        # #
        # # \param      _name    Member name. Must not be empty.
        # # \param      _type    Member type. Must not be empty. Can be any valid
        # #                      udt member type, like a pointer, array, etc.
        # # \param[in]  _offset  Member offset in bits. It is the caller's
        # #                      responsibility to specify correct offsets.
        # udm_t(const char *_name, const tinfo_t &_type, uint64 _offset) except +

        # # Create a structure/union member, with the specified name and simple type.
        # #
        # # The 'type' will be created from type_t, and the 'size' will
        # # be set automatically.
        # #
        # # \param      _name    Member name. Must not be empty.
        # # \param      _type    Member type. Must not be empty.
        # #                      Can be only a simple type (integral/floating/bool).
        # # \param[in]  _offset  Member offset in bits. It is the caller's
        # #                      responsibility to specify correct offsets.
        # udm_t(const char *_name, const type_t _type, uint64 _offset) except +

        # # Create a structure/union member, with the specified name and type.
        # #
        # # The 'type' object will be created by parsing the '_type' type
        # # declaration, and the 'size' will be set automatically.
        # #
        # # \param      _name    Member name. Must not be empty.
        # # \param      _type    Member type. Must not a valid C type declaration.
        # # \param[in]  _offset  Member offset in bits. It is the caller's
        # #                      responsibility to specify correct offsets.
        # udm_t(const char *_name, const char *_type, uint64 _offset) except +

        # a udt member must at least have a type
        bint empty() const

        bint is_bitfield() const
        bint is_zero_bitfield() const
        bint is_unaligned() const
        bint is_baseclass() const
        bint is_virtbase() const
        bint is_vftable() const
        bint is_method() const
        bint is_gap() const
        bint is_regcmt() const
        bint is_retaddr() const
        bint is_savregs() const
        bint is_special_member() const
        bint is_by_til() const

        void set_unaligned(bint on=True)
        void set_baseclass(bint on=True)
        void set_virtbase(bint on=True)
        void set_vftable(bint on=True)
        void set_method(bint on=True)
        void set_regcmt(bint on=True)
        void set_retaddr(bint on=True)
        void set_savregs(bint on=True)
        void set_by_til(bint on=True)
        void clr_unaligned()
        void clr_baseclass()
        void clr_virtbase()
        void clr_vftable()
        void clr_method()
        uint64 begin() const
        uint64 end() const
        bint operator<(const udm_t &r) const
        bint operator==(const udm_t &r) const
        bint operator!=(const udm_t &r) const

        # memory allocation and swap
        # DEFINE_MEMORY_ALLOCATION_FUNCS()
        void swap(udm_t &r)

        # the user cannot enter anonymous fields in ida (they can come only from tils),
        # so we use the following trick: if the field type starts with $ and the name
        # with __, then we consider the field as anonymous
        bint is_anonymous_udm() const

        void set_value_repr(const value_repr_t &r)
        bint can_be_dtor() const
        bint can_rename() const

    cdef cppclass rrel_t:
        sval_t off
        int reg

    cdef cppclass argloc_t:
        # Note: Only public data members and methods can be declared in cdef cppclass.
        # The actual C++ class has private members and unions, but for Cython interop,
        # we only declare what we need to access. The union is flattened as per Cython convention.

        # The type of argument location
        argloc_type_t type

        # The union members (flattened)
        sval_t sval           # ::ALOC_STACK, ::ALOC_STATIC
        uint32 reginfo        # ::ALOC_REG1, ::ALOC_REG2
        rrel_t* rrel          # ::ALOC_RREL
        scattered_aloc_t* dist # ::ALOC_DIST
        void* custom          # ::ALOC_CUSTOM
        size_t biggest        # to facilitate manipulation of this union

    cdef cppclass argpart_t(argloc_t):
        ushort off
        ushort size

    ctypedef qvector[argpart_t] argpartvec_t
    cdef cppclass scattered_aloc_t(argpartvec_t):
        pass

cdef extern from "xref.hpp":
    ctypedef qvector[svalvec_t] casevec_t

cdef extern from "idp.hpp":
    # Get register number and size from register name
    cdef cppclass reg_info_t:
        int reg    # register number
        int size   # register size

    ctypedef qvector[reg_info_t] reginfovec_t #< vector of register info objects

cdef extern from "range.hpp":
    # --------------------------------------------------------------------------
    # Base class for a range. This class is used as a base class for
    # a class with real information - see segment.hpp for example.
    # The end address is excluded, it points past the range end.
    cdef cppclass range_t:
        ea_t start_ea   # start_ea included
        ea_t end_ea     # end_ea excluded

    # Vector of range_t instances
    ctypedef qvector[range_t] rangevec_base_t
    cdef cppclass rangevec_t(rangevec_base_t):
        pass

cdef extern from "funcs.hpp":

    # ------------------------------------------------------------------------
    # A function is a set of continuous ranges of addresses with characteristics
    cdef cppclass func_t(range_t):
        # \ref FUNC_
        uint64 flags

        # Is a far function?
        bint is_far() const
        # Does function return?
        bint does_return() const
        # Has SP-analysis been performed?
        bint analyzed_sp() const
        # Needs prolog analysis?
        bint need_prolog_analysis() const

        # --- Function entry chunk attributes ---
        #
        # Stack frame of the function. It is represented as a structure:
        #
        #    +------------------------------------------------+
        #    | function arguments                             |
        #    +------------------------------------------------+
        #    | return address (isn't stored in func_t)        |
        #    +------------------------------------------------+
        #    | saved registers (SI, DI, etc - func_t::frregs) |
        #    +------------------------------------------------+ <- typical BP
        #    |                                                |  |
        #    |                                                |  | func_t::fpd
        #    |                                                |  |
        #    |                                                | <- real BP
        #    | local variables (func_t::frsize)               |
        #    |                                                |
        #    |                                                |
        #    +------------------------------------------------+ <- SP
        #
        uval_t frame           # netnode id of frame structure - see frame.hpp
        asize_t frsize         # size of local variables part of frame in bytes.
                              # If FUNC_FRAME is set and fpd==0, the frame pointer
                              # (EBP) is assumed to point to the top of the local
                              # variables range.
        ushort frregs          # size of saved registers in frame. This range is
                              # immediately above the local variables range.
        asize_t argsize        # number of bytes purged from the stack upon returning
        asize_t fpd            # frame pointer delta. (usually 0, i.e. realBP==typicalBP)
                              # use update_fpd() to modify it.

        # bgcolor_t color        # user defined function color

        # # The following fields should not be accessed directly:

        # uint32 pntqty          # number of SP change points
        # stkpnt_t* points       # array of SP change points.
        #                       # use ...stkpnt...() functions to access this array.

        # int regvarqty          # number of register variables (-1-not read in yet)
        #                       # use find_regvar() to read register variables
        # regvar_t* regvars      # array of register variables.
        #                       # this array is sorted by: start_ea.
        #                       # use ...regvar...() functions to access this array.

        # int llabelqty          # number of local labels
        # llabel_t* llabels      # local labels array.
        #                       # this array shouldn't be modified directly; name.hpp's
        #                       # SN_LOCAL should be used instead.

        # int regargqty          # number of register arguments.
        #                       # During analysis IDA tries to guess the register
        #                       # arguments. It stores the guessing outcome
        #                       # in this field. As soon as it determines the final
        #                       # function prototype, regargqty is set to zero.
        # regarg_t* regargs      # unsorted array of register arguments.
        #                       # use ...regarg...() functions to access this array.
        #                       # regargs are destroyed when the full function
        #                       # type is determined.

        # int tailqty            # number of function tails
        # range_t* tails         # array of tails, sorted by ea.
        #                       # use func_tail_iterator_t to access function tails.

        # # --- Function tail chunk attributes ---
        # ea_t owner             # the address of the main function possessing this tail
        # int refqty             # number of referers
        # ea_t* referers         # array of referers (function start addresses).
        #                       # use func_parent_iterator_t to access the referers.

cpdef enum class OPTI(unsigned int):
    ADDREXPRS = 0x0001  # optimize all address expressions (&x+N; &x-&y)
    MINSTKREF = 0x0002  # may update minstkref
    COMBINSNS = 0x0004  # may combine insns (only for optimize_insn)
    NO_LDXOPT = 0x0008  # the function is called after
                        # the propagation attempt, we do not optimize
                        # low/high(ldx) in this case
    NO_VALRNG = 0x0010  # forbid using valranges


# Declare the C++ structures from the Hex-Rays SDK.
cdef extern from "hexrays.hpp":
    ctypedef uint8 mopt_t

    ctypedef int mreg_t

    # Exact dummy sizes so struct packing matches the real SDK.
    cdef cppclass ivl_with_name_t:
        char _pad[32]              # sizeof(ivl_with_name_t) = 32

    cdef cppclass rlist_t:
        char _pad[16]              # sizeof(rlist_t) = 16

    cdef cppclass ivlset_t:
        char _pad[24]              # sizeof(ivlset_t) = 24

    cdef cppclass mlist_t:
        rlist_t reg
        ivlset_t mem
        const char *dstr() const;

    # Local variable locator.
    # Local variables are located using definition ea and location.
    # Each variable must have a unique locator, this is how we tell them apart.
    cdef cppclass lvar_locator_t:
        vdloc_t location      # Variable location.
        ea_t defea           # Definition address. Usually, this is the address
                             # of the instruction that initializes the variable.
                             # In some cases it can be a fictional address.


    # Definition of a local variable (register or stack) #var #lvar
    cdef cppclass lvar_t(lvar_locator_t):
        # friend class mba_t;  # Not expressible in Cython, skip

        int flags              # \ref CVAR_

        qstring name          # variable name.
                              # use mba_t::set_nice_lvar_name() and
                              # mba_t::set_user_lvar_name() to modify it
        qstring cmt           # variable comment string
        tinfo_t tif           # variable type
        int width             # variable size in bytes
        int defblk            # first block defining the variable.
                              # 0 for args, -1 if unknown
        uint64 divisor        # max known divisor of the variable


    # Vector of local variables
    ctypedef qvector[lvar_t] lvars_t

    cdef cppclass operand_locator_t:
        # Operand locator.
        # It is used to denote a particular operand in the ctree, for example,
        # when the user right clicks on a constant and requests to represent it,
        # say, as a hexadecimal number.

        ea_t ea     # Address of the original processor instruction
        int opnum   # Operand number in the instruction


    cpdef enum class mblock_type_t(unsigned int):
        BLT_NONE = 0 # unknown block type
        BLT_STOP = 1 # stops execution regularly (must be the last block)
        BLT_0WAY = 2 # does not have successors (tail is a noret function)
        BLT_1WAY = 3 # passes execution to one block (regular or goto block)
        BLT_2WAY = 4 # passes execution to two blocks (conditional jump)
        BLT_NWAY = 5 # passes execution to many blocks (switch idiom)
        BLT_XTRN = 6 # external block (out of function address)


    ## Function roles.
    ## They are used to calculate use/def lists and to recognize functions
    ## without using string comparisons.
    cpdef enum class funcrole_t(unsigned int):
        ROLE_UNK = 0                   # unknown function role
        ROLE_EMPTY = 1                 # empty, does not do anything (maybe spoils regs)
        ROLE_MEMSET = 2                # memset(void *dst, uchar value, size_t count);
        ROLE_MEMSET32 = 3              # memset32(void *dst, uint32 value, size_t count);
        ROLE_MEMSET64 = 4              # memset64(void *dst, uint64 value, size_t count);
        ROLE_MEMCPY = 5                # memcpy(void *dst, const void *src, size_t count);
        ROLE_STRCPY = 6                # strcpy(char *dst, const char *src);
        ROLE_STRLEN = 7                # strlen(const char *src);
        ROLE_STRCAT = 8                # strcat(char *dst, const char *src);
        ROLE_TAIL = 9                  # char *tail(const char *str);
        ROLE_BUG = 10                  # BUG() helper macro: never returns, causes exception
        ROLE_ALLOCA = 11               # alloca() function
        ROLE_BSWAP = 12                # bswap() function (any size)
        ROLE_PRESENT = 13              # present() function (used in patterns)
        ROLE_CONTAINING_RECORD = 14    # CONTAINING_RECORD() macro
        ROLE_FASTFAIL = 15             # __fastfail()
        ROLE_READFLAGS = 16            # __readeflags, __readcallersflags
        ROLE_IS_MUL_OK = 17            # is_mul_ok
        ROLE_SATURATED_MUL = 18        # saturated_mul
        ROLE_BITTEST = 19              # [lock] bt
        ROLE_BITTESTANDSET = 20        # [lock] bts
        ROLE_BITTESTANDRESET = 21      # [lock] btr
        ROLE_BITTESTANDCOMPLEMENT = 22 # [lock] btc
        ROLE_VA_ARG = 23               # va_arg() macro
        ROLE_VA_COPY = 24              # va_copy() function
        ROLE_VA_START = 25             # va_start() function
        ROLE_VA_END = 26               # va_end() function
        ROLE_ROL = 27                  # rotate left
        ROLE_ROR = 28                  # rotate right
        ROLE_CFSUB3 = 29               # carry flag after subtract with carry
        ROLE_OFSUB3 = 30               # overflow flag after subtract with carry
        ROLE_ABS = 31                  # integer absolute value
        ROLE_3WAYCMP0 = 32             # 3-way compare helper, returns -1/0/1
        ROLE_3WAYCMP1 = 33             # 3-way compare helper, returns 0/1/2
        ROLE_WMEMCPY = 34              # wchar_t *wmemcpy(wchar_t *dst, const wchar_t *src, size_t n)
        ROLE_WMEMSET = 35              # wchar_t *wmemset(wchar_t *dst, wchar_t wc, size_t n)
        ROLE_WCSCPY = 36               # wchar_t *wcscpy(wchar_t *dst, const wchar_t *src);
        ROLE_WCSLEN = 37               # size_t wcslen(const wchar_t *s)
        ROLE_WCSCAT = 38               # wchar_t *wcscat(wchar_t *dst, const wchar_t *src)
        ROLE_SSE_CMP4 = 39             # e.g. _mm_cmpgt_ss
        ROLE_SSE_CMP8 = 40             # e.g. _mm_cmpgt_sd

    #-------------------------------------------------------------------------
    # We use our own class to store argument and variable locations.
    # It is called vdloc_t that stands for 'vd location'.
    # 'vd' is the internal name of the decompiler, it stands for 'visual decompiler'.
    # The main differences between vdloc and argloc_t:
    #   ALOC_REG1: the offset is always 0, so it is not used. the register number
    #              uses the whole ~VLOC_MASK field.
    #   ALOC_STACK: stack offsets are always positive because they are based on
    #              the lowest value of sp in the function.
    cdef cppclass vdloc_t(argloc_t):
        pass

    cdef cppclass lvar_ref_t:
        # Pointer to the parent mba_t object.
        # Since we need to access the 'mba->vars' array in order to retrieve
        # the referenced variable, we keep a pointer to mba_t here.
        # Note: this means this class and consequently mop_t, minsn_t, mblock_t
        #       are specific to a mba_t object and cannot migrate between
        #       them. fortunately this is not something we need to do.
        #       second, lvar_ref_t's appear only after MMAT_LVARS.
        mba_t* mba  # mba_t *const mba

        sval_t off  # offset from the beginning of the variable
        int idx     # index into mba->vars

    # Scattered operand info. Used for mop_sc
    cdef cppclass scif_t(vdloc_t):
        # Pointer to the parent mba_t object.
        # Some operations may convert a scattered operand into something simpler,
        # (a stack operand, for example). We will need to create stkvar_ref_t at
        # that moment, this is why we need this pointer.
        # See notes for lvar_ref_t::mba.
        mba_t* mba
        # Usually scattered operands are created from a function prototype,
        # which has the name information. We preserve it and use it to name
        # the corresponding local variable.
        qstring name

        # Scattered operands always have type info assigned to them
        # because without it we won't be able to manipulate them.
        tinfo_t type

    # --- mop_t and its internal union members ---
    cdef struct stkvar_ref_t:
        # Pointer to the parent mba_t object.
        # We need it in order to retrieve the referenced stack variable.
        # See notes for lvar_ref_t::mba.
        mba_t* mba  # mba_t* const mba

        # Offset to the stack variable from the bottom of the stack frame.
        # It is called 'decompiler stkoff' and it is different from IDA stkoff.
        # See a note and a picture about 'decompiler stkoff' below.
        sval_t off
        # Swap the contents of this stkvar_ref_t with another.
        void swap(stkvar_ref_t &r)

        # Retrieve the referenced stack variable.
        # \param[out] udm  stkvar, may be nullptr
        # \param p_idaoff if specified, will hold IDA stkoff after the call.
        # \return index of stkvar in the frame or -1
        ssize_t get_stkvar(udm_t *udm, uval_t *p_idaoff)

    cdef cppclass mnumber_t(operand_locator_t):
        uint64 value  # value
        uint64 org_value  # original value before changing the operand size

    #-------------------------------------------------------------------------
    # Floating point constant. Used for mop_fn
    # For more details, please see the ieee.h file from IDA SDK.
    cdef cppclass fnumber_t:
        fpvalue_t fnum    # Internal representation of the number
        int nbytes        # Original size of the constant in bytes
        # Get displayable text without tags in a static buffer
        const char *dstr() const
    # Pair of operands
    cdef cppclass mop_pair_t:
        mop_t lop      # low operand
        mop_t hop      # high operand
        # HEXRAYS_MEMORY_ALLOCATION_FUNCS() is a macro for custom new/delete, not needed in .pxd

    cdef cppclass mop_t:
        mop_t() except +
        mopt_t t         # operand type
        uint8 oprops
        uint16 valnum
        int size
        # The following union holds additional details about the operand.
        # Depending on the operand type different kinds of info are stored.
        # You should access these fields only after verifying the operand type.
        # All pointers are owned by the operand and are freed by its destructor.

        mreg_t r           # mop_r   register number
        mnumber_t *nnn     # mop_n   immediate value
        minsn_t *d         # mop_d   result (destination) of another instruction
        stkvar_ref_t *s    # mop_S   stack variable
        ea_t g             # mop_v   global variable (its linear address)
        int b              # mop_b   block number (used in jmp,call instructions)
        mcallinfo_t *f     # mop_f   function call information
        lvar_ref_t *l      # mop_l   local variable
        mop_addr_t *a      # mop_a   variable whose address is taken
        char *helper       # mop_h   helper function name
        char *cstr         # mop_str utf8 string constant, user representation
        mcases_t *c        # mop_c   cases
        fnumber_t *fpc     # mop_fn  floating point constant
        mop_pair_t *pair   # mop_p   operand pair
        scif_t *scif       # mop_sc  scattered operand info
        # Get displayable text without tags in a static buffer
        const char *dstr() const
        void make_number(uint64 val, int size)
        void assign(const mop_t& other)


    # Address of an operand (mop_l, mop_v, mop_S, mop_r)
    cdef cppclass mop_addr_t(mop_t):
        int insize     # how many bytes of the pointed operand can be read
        int outsize    # how many bytes of the pointed operand can be written

    # A call argument
    cdef cppclass mcallarg_t(mop_t):  # #callarg
        ea_t ea      # address where the argument was initialized. BADADDR means unknown.
        tinfo_t type # formal argument type
        qstring name # formal argument name
        argloc_t argloc # ida argloc
        uint32 flags # FAI_...
        # Get displayable text without tags in a static buffer
        const char *dstr() const

    ctypedef qvector[mop_t] mopvec_t;
    ctypedef qvector[mcallarg_t] mcallargs_t;
    # Information about a call
    cdef cppclass mcallinfo_t:
        ea_t callee
        int solid_args
        int call_spd
        int stkargs_top
        cm_t cc
        mcallargs_t args
        mopvec_t retregs
        tinfo_t return_type
        argloc_t return_argloc
        mlist_t return_regs
        mlist_t spoiled
        mlist_t pass_regs
        ivlset_t visible_memory
        mlist_t dead_regs
        int flags
        funcrole_t role
        type_attrs_t fti_attrs
        # Get displayable text without tags in a static buffer
        const char *dstr() const


    # List of switch cases and targets
    cdef cppclass mcases_t:
        casevec_t values
        intvec_t targets

    # -------------------------------------------------------------------------
    # \defgroup MERR_ Microcode error codes
    #@{
    ctypedef enum merror_t:
        MERR_OK        = 0    # ok
        MERR_BLOCK     = 1    # no error, switch to new block
        MERR_INTERR    = -1   # internal error
        MERR_INSN      = -2   # cannot convert to microcode
        MERR_MEM       = -3   # not enough memory
        MERR_BADBLK    = -4   # bad block found
        MERR_BADSP     = -5   # positive sp value has been found
        MERR_PROLOG    = -6   # prolog analysis failed
        MERR_SWITCH    = -7   # wrong switch idiom
        MERR_EXCEPTION = -8   # exception analysis failed
        MERR_HUGESTACK = -9   # stack frame is too big
        MERR_LVARS     = -10  # local variable allocation failed
        MERR_BITNESS   = -11  # 16-bit functions cannot be decompiled
        MERR_BADCALL   = -12  # could not determine call arguments
        MERR_BADFRAME  = -13  # function frame is wrong
        MERR_UNKTYPE   = -14  # undefined type %s (currently unused error code)
        MERR_BADIDB    = -15  # inconsistent database information
        MERR_SIZEOF    = -16  # wrong basic type sizes in compiler settings
        MERR_REDO      = -17  # redecompilation has been requested
        MERR_CANCELED  = -18  # decompilation has been cancelled
        MERR_RECDEPTH  = -19  # max recursion depth reached during lvar allocation
        MERR_OVERLAP   = -20  # variables would overlap: %s
        MERR_PARTINIT  = -21  # partially initialized variable %s
        MERR_COMPLEX   = -22  # too complex function
        MERR_LICENSE   = -23  # no license available
        MERR_ONLY32    = -24  # only 32-bit functions can be decompiled for the current database
        MERR_ONLY64    = -25  # only 64-bit functions can be decompiled for the current database
        MERR_BUSY      = -26  # already decompiling a function
        MERR_FARPTR    = -27  # far memory model is supported only for pc
        MERR_EXTERN    = -28  # special segments cannot be decompiled
        MERR_FUNCSIZE  = -29  # too big function
        MERR_BADRANGES = -30  # bad input ranges
        MERR_BADARCH   = -31  # current architecture is not supported
        MERR_DSLOT     = -32  # bad instruction in the delay slot
        MERR_STOP      = -33  # no error, stop the analysis
        MERR_CLOUD     = -34  # cloud: %s
        MERR_MAX_ERR   = 34
        MERR_LOOP      = -35  # internal code: redo last loop (never reported)
    #@}

    # Get textual description of an error code
    # \param out  the output buffer for the error description
    # \param code \ref MERR_
    # \param mba  the microcode array
    # \return the error address
    ea_t get_merror_desc(qstring *out, merror_t code, mba_t *mba)

    # -------------------------------------------------------------------------
    # List of microinstruction opcodes.
    # The order of setX and jX insns is important, it is used in the code.

    # Instructions marked with *F may have the FPINSN bit set and operate on fp values
    # Instructions marked with +F must have the FPINSN bit set. They always operate on fp values
    # Other instructions do not operate on fp values.
    ctypedef enum mcode_t:
        m_nop    # nop                       // no operation
        m_stx    # stx  l,    {r=sel, d=off} // store register to memory     *F
        m_ldx    # ldx  {l=sel,r=off}, d     // load register from memory    *F
        m_ldc    # ldc  l=const,     d       // load constant
        m_mov    # mov  l,           d       // move                         *F
        m_neg    # neg  l,           d       // negate
        m_lnot   # lnot l,           d       // logical not
        m_bnot   # bnot l,           d       // bitwise not
        m_xds    # xds  l,           d       // extend (signed)
        m_xdu    # xdu  l,           d       // extend (unsigned)
        m_low    # low  l,           d       // take low part
        m_high   # high l,           d       // take high part
        m_add    # add  l,   r,      d       // l + r -> dst
        m_sub    # sub  l,   r,      d       // l - r -> dst
        m_mul    # mul  l,   r,      d       // l * r -> dst
        m_udiv   # udiv l,   r,      d       // l / r -> dst
        m_sdiv   # sdiv l,   r,      d       // l / r -> dst
        m_umod   # umod l,   r,      d       // l % r -> dst
        m_smod   # smod l,   r,      d       // l % r -> dst
        m_or     # or   l,   r,      d       // bitwise or
        m_and    # and  l,   r,      d       // bitwise and
        m_xor    # xor  l,   r,      d       // bitwise xor
        m_shl    # shl  l,   r,      d       // shift logical left
        m_shr    # shr  l,   r,      d       // shift logical right
        m_sar    # sar  l,   r,      d       // shift arithmetic right
        m_cfadd  # cfadd l,  r,    d=carry   // calculate carry    bit of (l+r)
        m_ofadd  # ofadd l,  r,    d=overf   // calculate overflow bit of (l+r)
        m_cfshl  # cfshl l,  r,    d=carry   // calculate carry    bit of (l<<r)
        m_cfshr  # cfshr l,  r,    d=carry   // calculate carry    bit of (l>>r)
        m_sets   # sets  l,          d=byte  SF=1          Sign
        m_seto   # seto  l,  r,      d=byte  OF=1          Overflow of (l-r)
        m_setp   # setp  l,  r,      d=byte  PF=1          Unordered/Parity        *F
        m_setnz  # setnz l,  r,      d=byte  ZF=0          Not Equal               *F
        m_setz   # setz  l,  r,      d=byte  ZF=1          Equal                   *F
        m_setae  # setae l,  r,      d=byte  CF=0          Unsigned Above or Equal *F
        m_setb   # setb  l,  r,      d=byte  CF=1          Unsigned Below          *F
        m_seta   # seta  l,  r,      d=byte  CF=0 & ZF=0   Unsigned Above          *F
        m_setbe  # setbe l,  r,      d=byte  CF=1 | ZF=1   Unsigned Below or Equal *F
        m_setg   # setg  l,  r,      d=byte  SF=OF & ZF=0  Signed Greater
        m_setge  # setge l,  r,      d=byte  SF=OF         Signed Greater or Equal
        m_setl   # setl  l,  r,      d=byte  SF!=OF        Signed Less
        m_setle  # setle l,  r,      d=byte  SF!=OF | ZF=1 Signed Less or Equal
        m_jcnd   # jcnd   l,         d       // d is mop_v or mop_b
        m_jnz    # jnz    l, r,      d       // ZF=0          Not Equal               *F
        m_jz     # jz     l, r,      d       // ZF=1          Equal                   *F
        m_jae    # jae    l, r,      d       // CF=0          Unsigned Above or Equal *F
        m_jb     # jb     l, r,      d       // CF=1          Unsigned Below          *F
        m_ja     # ja     l, r,      d       // CF=0 & ZF=0   Unsigned Above          *F
        m_jbe    # jbe    l, r,      d       // CF=1 | ZF=1   Unsigned Below or Equal *F
        m_jg     # jg     l, r,      d       // SF=OF & ZF=0  Signed Greater
        m_jge    # jge    l, r,      d       // SF=OF         Signed Greater or Equal
        m_jl     # jl     l, r,      d       // SF!=OF        Signed Less
        m_jle    # jle    l, r,      d       // SF!=OF | ZF=1 Signed Less or Equal
        m_jtbl   # jtbl   l, r=mcases        // Table jump
        m_ijmp   # ijmp       {r=sel, d=off} // indirect unconditional jump
        m_goto   # goto   l                  // l is mop_v or mop_b
        m_call   # call   l          d       // l is mop_v or mop_b or mop_h
        m_icall  # icall  {l=sel, r=off} d   // indirect call
        m_ret    # ret
        m_push   # push   l
        m_pop    # pop               d
        m_und    # und               d       // undefine
        m_ext    # ext  in1, in2,  out1      // external insn, not microcode *F
        m_f2i    # f2i    l,    d       int(l) => d; convert fp -> integer   +F
        m_f2u    # f2u    l,    d       uint(l)=> d; convert fp -> uinteger  +F
        m_i2f    # i2f    l,    d       fp(l)  => d; convert integer -> fp   +F
        m_u2f    # i2f    l,    d       fp(l)  => d; convert uinteger -> fp  +F
        m_f2f    # f2f    l,    d       l      => d; change fp precision     +F
        m_fneg   # fneg   l,    d       -l     => d; change sign             +F
        m_fadd   # fadd   l, r, d       l + r  => d; add                     +F
        m_fsub   # fsub   l, r, d       l - r  => d; subtract                +F
        m_fmul   # fmul   l, r, d       l * r  => d; multiply                +F
        m_fdiv   # fdiv   l, r, d       l / r  => d; divide                  +F


    # --- Other Hex-Rays types ---
    cdef cppclass minsn_t:
        mcode_t opcode
        int iprops           # combination of IPROP_ bits
        minsn_t *next        # next insn in doubly linked list. check also nexti()
        minsn_t *prev        # prev insn in doubly linked list. check also previ()
        ea_t ea              # instruction address
        mop_t l              # left operand
        mop_t r              # right operand
        mop_t d              # destination operand

        # Get displayable text without tags in a static buffer
        const char *dstr() const

        # Change the instruction address.
        # This function modifies subinstructions as well.
        void setaddr(ea_t new_ea)

        # Optimize one instruction without context.
        # This function does not have access to the instruction context (the
        # previous and next instructions in the list, the block number, etc).
        # It performs only basic optimizations that are available without this info.
        # \param optflags combination of \ref OPTI_ bits
        # \return number of changes, 0-unchanged
        # See also mblock_t::optimize_insn()
        int optimize_solo(int optflags)

        # Does the instruction have a side effect?
        # \param include_ldx_and_divs consider ldx/div/mod as having side effects?
        #                    stx is always considered as having side effects.
        # Apart from ldx/std only call may have side effects.
        bint has_side_effects(bint include_ldx_and_divs) const

        # Is a helper call with the specified name?
        # Helper calls usually have well-known function names (see \ref FUNC_NAME_)
        # but they may have any other name. The decompiler does not assume any
        # special meaning for non-well-known names.
        bint is_helper(const char *name) const

        # Is an unknown call?
        # Unknown calls are calls without the argument list (mcallinfo_t).
        # Usually the argument lists are determined by mba_t::analyze_calls().
        # Unknown calls exist until the MMAT_CALLS maturity level.
        # See also \ref mblock_t::is_call_block
        bint is_unknown_call() const

    cdef cppclass mblock_t:
        mblock_t *nextb              #< next block in the doubly linked list
        mblock_t *prevb              #< previous block in the doubly linked list
        uint32 flags                 #< combination of \ref MBL_ bits
        ea_t start                   #< start address
        ea_t end                     #< end address
        minsn_t* head                #< pointer to the first instruction of the block
        minsn_t* tail                #< pointer to the last instruction of the block
        mba_t* mba                   #< the parent micro block array
        int serial                   #< block number
        mblock_type_t type           #< block type (BLT_NONE - not computed yet)
        mlist_t dead_at_start        #< data that is dead at the block entry
        mlist_t mustbuse             #< data that must be used by the block
        mlist_t maybuse              #< data that may  be used by the block
        mlist_t mustbdef             #< data that must be defined by the block
        mlist_t maybdef              #< data that may  be defined by the block
        mlist_t dnu                  #< data that is defined but not used in the block
        sval_t maxbsp                #< maximal sp value in the block (0...stacksize)
        sval_t minbstkref            #< lowest stack location accessible with indirect
                                      #< addressing (offset from the stack bottom)
                                      #< initially it is 0 (not computed)
        sval_t minbargref            #< the same for arguments
        intvec_t predset             #< control flow graph: list of our predecessors
                                      #< use npred() and pred() to access it
        intvec_t succset             #< control flow graph: list of our successors


        # Mark the block's use-def lists as dirty and request propagation
        void mark_lists_dirty()
        # Request propagation for the block
        void request_propagation()
        # Check if propagation is needed
        bint needs_propagation() const
        # Request demotion to 64-bit
        void request_demote64()
        # Check if lists are dirty
        bint lists_dirty() const
        # Check if lists are ready
        bint lists_ready() const
        # Make lists ready, returns number of changes
        int make_lists_ready()

        # Get number of block predecessors (number of xrefs to the block)
        int npred() const
        # Get number of block successors (number of xrefs from the block)
        int nsucc() const
        # Get predecessor number N
        int pred(int n) const
        # Get successor number N
        int succ(int n) const

        # mblock_t() = delete; -- not needed in Cython
        # Virtual destructor
        # (Cython: use 'cppclass' destructor syntax)
        # ~mblock_t();
        # HEXRAYS_MEMORY_ALLOCATION_FUNCS() -- not needed in Cython
        # Check if block is empty
        bint empty() const

        # Print block contents.
        # \param vp print helpers class. it can be used to direct the printed info to any destination
        # void print(vd_printer_t &vp) const

        # Dump block info.
        # This function is useful for debugging, see mba_t::dump for info
        void dump() const
        # Print block with va_list
        void vdump_block(const char *title, ...) const
        # Print block with variadic arguments
        void dump_block(const char *title, ...) const

        #-----------------------------------------------------------------------
        # Functions to insert/remove insns during the microcode optimization phase.
        # See codegen_t, microcode_filter_t, udcall_t classes for the initial
        # microcode generation.
        #-----------------------------------------------------------------------
        # Insert instruction into the doubly linked list
        # \param nm new instruction
        # \param om existing instruction, part of the doubly linked list
        #           if nullptr, then the instruction will be inserted at the beginning
        # NM will be inserted immediately after OM
        # \return pointer to NM
        minsn_t *insert_into_block(minsn_t *nm, minsn_t *om)

        # Remove instruction from the doubly linked list
        # \param m instruction to remove
        # The removed instruction is not deleted, the caller gets its ownership
        # \return pointer to the next instruction
        minsn_t *remove_from_block(minsn_t *m)

        #-----------------------------------------------------------------------
        # Iterator over instructions and operands
        #-----------------------------------------------------------------------
        # Visit all instructions.
        # This function visits subinstructions too.
        # \param mv instruction visitor
        # \return zero or the value returned by mv.visit_insn()
        # See also mba_t::for_all_topinsns()
        #int for_all_insns(minsn_visitor_t &mv)

        # Visit all operands.
        # This function visit subinstruction operands too.
        # \param mv operand visitor
        # \return zero or the value returned by mv.visit_mop()
        #int for_all_ops(mop_visitor_t &mv)

        # Visit all operands that use LIST.
        # \param list ptr to the list of locations. it may be modified:
        #             parts that get redefined by the instructions in [i1,i2)
        #             will be deleted.
        # \param i1   starting instruction. must be a top level insn.
        # \param i2   ending instruction (excluded). must be a top level insn.
        # \param mmv  operand visitor
        # \return zero or the value returned by mmv.visit_mop()
        # int for_all_uses(
        #         mlist_t *list,
        #         minsn_t *i1,
        #         minsn_t *i2,
        #         mlist_mop_visitor_t &mmv)

        #-----------------------------------------------------------------------
        # Optimization functions
        #-----------------------------------------------------------------------
        # Optimize one instruction in the context of the block.
        # \param m pointer to a top level instruction
        # \param optflags combination of \ref OPTI_ bits
        # \return number of changes made to the block
        # This function may change other instructions in the block too.
        # However, it will not destroy top level instructions (it may convert them
        # to nop's). This function performs only intrablock modifications.
        # See also minsn_t::optimize_solo()
        int optimize_insn(minsn_t *m, int optflags=OPTI.MINSTKREF|OPTI.COMBINSNS)

        # Optimize a basic block.
        # Usually there is no need to call this function explicitly because the
        # decompiler will call it itself if optinsn_t::func or optblock_t::func
        # return non-zero.
        # \return number of changes made to the block
        int optimize_block()

        # Build def-use lists and eliminate deads.
        # \param kill_deads do delete dead instructions?
        # \return the number of eliminated instructions
        # Better mblock_t::call make_lists_ready() rather than this function.
        int build_lists(bint kill_deads)

        # Remove a jump at the end of the block if it is useless.
        # This function preserves any side effects when removing a useless jump.
        # Both conditional and unconditional jumps are handled (and jtbl too).
        # This function deletes useless jumps, not only replaces them with a nop.
        # (please note that \optimize_insn does not handle useless jumps).
        # \return number of changes made to the block
        int optimize_useless_jump()

        #-----------------------------------------------------------------------
        # Functions that build with use/def lists. These lists are used to
        # reprsent list of registers and stack locations that are either modified
        # or accessed by microinstructions.
        #-----------------------------------------------------------------------
        # Append use-list of an operand.
        # This function calculates list of locations that may or must be used
        # by the operand and appends it to LIST.
        # \param list    ptr to the output buffer. we will append to it.
        # \param op      operand to calculate the use list of
        # \param maymust should we calculate 'may-use' or 'must-use' list?
        #                see \ref maymust_t for more details.
        # \param mask    if only part of the operand should be considered,
        #                a bitmask can be used to specify which part.
        #                example: op=AX,mask=0xFF means that we will consider only AL.
        # void append_use_list(
        #         mlist_t *list,
        #         mop_t& op,
        #         maymust_t maymust,
        #         bitrange_t mask=MAXRANGE) const

        # Append def-list of an operand.
        # This function calculates list of locations that may or must be modified
        # by the operand and appends it to LIST.
        # \param list    ptr to the output buffer. we will append to it.
        # \param op      operand to calculate the def list of
        # \param maymust should we calculate 'may-def' or 'must-def' list?
        #                see \ref maymust_t for more details.
        # void append_def_list(
        #         mlist_t *list,
        #         mop_t& op,
        #         maymust_t maymust) const

        # Build use-list of an instruction.
        # This function calculates list of locations that may or must be used
        # by the instruction. Examples:
        #   "ldx ds.2, eax.4, ebx.4", may-list: all aliasable memory
        #   "ldx ds.2, eax.4, ebx.4", must-list: empty
        # Since LDX uses EAX for indirect access, it may access any aliasable
        # memory. On the other hand, we cannot tell for sure which memory cells
        # will be accessed, this is why the must-list is empty.
        # \param ins     instruction to calculate the use list of
        # \param maymust should we calculate 'may-use' or 'must-use' list?
        #                see \ref maymust_t for more details.
        # \return the calculated use-list
        # mlist_t build_use_list(const minsn_t& ins, maymust_t maymust) const

        # Build def-list of an instruction.
        # This function calculates list of locations that may or must be modified
        # by the instruction. Examples:
        #   "stx ebx.4, ds.2, eax.4", may-list: all aliasable memory
        #   "stx ebx.4, ds.2, eax.4", must-list: empty
        # Since STX uses EAX for indirect access, it may modify any aliasable
        # memory. On the other hand, we cannot tell for sure which memory cells
        # will be modified, this is why the must-list is empty.
        # \param ins     instruction to calculate the def list of
        # \param maymust should we calculate 'may-def' or 'must-def' list?
        #                see \ref maymust_t for more details.
        # \return the calculated def-list
        # mlist_t build_def_list(const minsn_t& ins, maymust_t maymust) const

        #-----------------------------------------------------------------------
        # The use/def lists can be used to search for interesting instructions
        #-----------------------------------------------------------------------
        # Is the list used by the specified instruction range?
        # \param list list of locations. LIST may be modified by the function:
        #             redefined locations will be removed from it.
        # \param i1   starting instruction of the range (must be a top level insn)
        # \param i2   end instruction of the range (must be a top level insn)
        #             i2 is excluded from the range. it can be specified as nullptr.
        #             i1 and i2 must belong to the same block.
        # \param maymust should we search in 'may-access' or 'must-access' mode?
        # bint is_used(mlist_t *list, const minsn_t *i1, const minsn_t *i2, maymust_t maymust=MAY_ACCESS) const

        # Find the first insn that uses the specified list in the insn range.
        # \param list list of locations. LIST may be modified by the function:
        #             redefined locations will be removed from it.
        # \param i1   starting instruction of the range (must be a top level insn)
        # \param i2   end instruction of the range (must be a top level insn)
        #             i2 is excluded from the range. it can be specified as nullptr.
        #             i1 and i2 must belong to the same block.
        # \param maymust should we search in 'may-access' or 'must-access' mode?
        # \return pointer to such instruction or nullptr.
        #         Upon return LIST will contain only locations not redefined
        #         by insns [i1..result]
        # const minsn_t *find_first_use(mlist_t *list, const minsn_t *i1, const minsn_t *i2, maymust_t maymust=MAY_ACCESS) const
        # minsn_t *find_first_use(mlist_t *list, minsn_t *i1, const minsn_t *i2, maymust_t maymust=MAY_ACCESS) const

        # Is the list redefined by the specified instructions?
        # \param list list of locations to check.
        # \param i1   starting instruction of the range (must be a top level insn)
        # \param i2   end instruction of the range (must be a top level insn)
        #             i2 is excluded from the range. it can be specified as nullptr.
        #             i1 and i2 must belong to the same block.
        # \param maymust should we search in 'may-access' or 'must-access' mode?
        # bint is_redefined(
        #         const mlist_t &list,
        #         const minsn_t *i1,
        #         const minsn_t *i2,
        #         maymust_t maymust=MAY_ACCESS) const

        # Find the first insn that redefines any part of the list in the insn range.
        # \param list list of locations to check.
        # \param i1   starting instruction of the range (must be a top level insn)
        # \param i2   end instruction of the range (must be a top level insn)
        #             i2 is excluded from the range. it can be specified as nullptr.
        #             i1 and i2 must belong to the same block.
        # \param maymust should we search in 'may-access' or 'must-access' mode?
        # \return pointer to such instruction or nullptr.
        # const minsn_t *find_redefinition(
        #         const mlist_t &list,
        #         const minsn_t *i1,
        #         const minsn_t *i2,
        #         maymust_t maymust=MAY_ACCESS) const
        # minsn_t *find_redefinition(
        #         const mlist_t &list,
        #         minsn_t *i1,
        #         const minsn_t *i2,
        #         maymust_t maymust=MAY_ACCESS) const

        # Is the right hand side of the instruction redefined the insn range?
        # "right hand side" corresponds to the source operands of the instruction.
        # \param ins instruction to consider
        # \param i1   starting instruction of the range (must be a top level insn)
        # \param i2   end instruction of the range (must be a top level insn)
        #             i2 is excluded from the range. it can be specified as nullptr.
        #             i1 and i2 must belong to the same block.
        bint is_rhs_redefined(const minsn_t *ins, const minsn_t *i1, const minsn_t *i2) const

        # Find the instruction that accesses the specified operand.
        # This function search inside one block.
        # \param op     operand to search for
        # \param[in,out] parent ptr to ptr to a top level instruction.
        #               in: denotes the beginning of the search range.
        #               out: denotes the parent of the found instruction.
        # \param mend   end instruction of the range (must be a top level insn)
        #               mend is excluded from the range. it can be specified as nullptr.
        #               parent and mend must belong to the same block.
        # \param fdflags combination of \ref FD_ bits
        # \return       the instruction that accesses the operand. this instruction
        #               may be a sub-instruction. to find out the top level
        #               instruction, check out *parent.
        #               nullptr means 'not found'.
        minsn_t *find_access(
                mop_t& op,
                minsn_t **parent,
                const minsn_t *mend,
                int fdflags) const

        # FD_ bits for mblock_t::find_access
        #define FD_BACKWARD 0x0000  # search direction
        #define FD_FORWARD  0x0001  # search direction
        #define FD_USE      0x0000  # look for use
        #define FD_DEF      0x0002  # look for definition
        #define FD_DIRTY    0x0004  # ignore possible implicit definitions by function calls and indirect memory access

        # Convenience functions:
        minsn_t *find_def(
                mop_t& op,
                minsn_t **p_i1,
                const minsn_t *i2,
                int fdflags)
        minsn_t *find_use(
                mop_t& op,
                minsn_t **p_i1,
                const minsn_t *i2,
                int fdflags)

        # Find possible values for a block.
        # \param res     set of value ranges
        # \param vivl    what to search for
        # \param vrflags combination of \ref VR_ bits
        # bint get_valranges(
        #         valrng_t *res,
        #         vivl_t& vivl,
        #         int vrflags) const

        # Find possible values for an instruction.
        # \param res     set of value ranges
        # \param vivl    what to search for
        # \param m       insn to search value ranges at. \sa VR_ bits
        # \param vrflags combination of \ref VR_ bits
        # bint get_valranges(
        #         valrng_t *res,
        #         vivl_t& vivl,
        #         const minsn_t *m,
        #         int vrflags) const

        # VR_ bits for get_valranges
        #define VR_AT_START 0x0000    # get value ranges before the instruction or at the block start (if M is nullptr)
        #define VR_AT_END   0x0001    # get value ranges after the instruction or at the block end, just after the last instruction (if M is nullptr)
        #define VR_EXACT    0x0002    # find exact match. if not set, the returned valrng size will be >= vivl.size

        # Erase the instruction (convert it to nop) and mark the lists dirty.
        # This is the recommended function to use because it also marks the block use-def lists dirty.
        void make_nop(minsn_t *m)

        # Calculate number of regular instructions in the block.
        # Assertions are skipped by this function.
        # \return Number of non-assertion instructions in the block.
        size_t get_reginsn_qty() const

        # Check if block is a call block
        bint is_call_block() const
        # Check if block is an unknown call
        bint is_unknown_call() const
        # Check if block is nway
        bint is_nway() const
        # Check if block is a branch
        bint is_branch() const
        # Check if block is a simple goto block
        bint is_simple_goto_block() const
        # Check if block is a simple jcnd block
        bint is_simple_jcnd_block() const

    #-------------------------------------------------------------------------
    # Warning ids
    cdef enum warnid_t:
        WARN_VARARG_REGS         #  0 cannot handle register arguments in vararg function, discarded them
        WARN_ILL_PURGED          #  1 odd caller purged bytes %d, correcting
        WARN_ILL_FUNCTYPE        #  2 invalid function type '%s' has been ignored
        WARN_VARARG_TCAL         #  3 cannot handle tail call to vararg
        WARN_VARARG_NOSTK        #  4 call vararg without local stack
        WARN_VARARG_MANY         #  5 too many varargs, some ignored
        WARN_ADDR_OUTARGS        #  6 cannot handle address arithmetics in outgoing argument area of stack frame -- unused
        WARN_DEP_UNK_CALLS       #  7 found interdependent unknown calls
        WARN_ILL_ELLIPSIS        #  8 erroneously detected ellipsis type has been ignored
        WARN_GUESSED_TYPE        #  9 using guessed type %s;
        WARN_EXP_LINVAR          # 10 failed to expand a linear variable
        WARN_WIDEN_CHAINS        # 11 failed to widen chains
        WARN_BAD_PURGED          # 12 inconsistent function type and number of purged bytes
        WARN_CBUILD_LOOPS        # 13 too many cbuild loops
        WARN_NO_SAVE_REST        # 14 could not find valid save-restore pair for %s
        WARN_ODD_INPUT_REG       # 15 odd input register %s
        WARN_ODD_ADDR_USE        # 16 odd use of a variable address
        WARN_MUST_RET_FP         # 17 function return type is incorrect (must be floating point)
        WARN_ILL_FPU_STACK       # 18 inconsistent fpu stack
        WARN_SELFREF_PROP        # 19 self-referencing variable has been detected
        WARN_WOULD_OVERLAP       # 20 variables would overlap: %s
        WARN_ARRAY_INARG         # 21 array has been used for an input argument
        WARN_MAX_ARGS            # 22 too many input arguments, some ignored
        WARN_BAD_FIELD_TYPE      # 23 incorrect structure member type for %s::%s, ignored
        WARN_WRITE_CONST         # 24 write access to const memory at %a has been detected
        WARN_BAD_RETVAR          # 25 wrong return variable
        WARN_FRAG_LVAR           # 26 fragmented variable at %s may be wrong
        WARN_HUGE_STKOFF         # 27 exceedingly huge offset into the stack frame
        WARN_UNINITED_REG        # 28 reference to an uninitialized register has been removed: %s
        WARN_FIXED_INSN          # 29 fixed broken insn
        WARN_WRONG_VA_OFF        # 30 wrong offset of va_list variable
        WARN_CR_NOFIELD          # 31 CONTAINING_RECORD: no field '%s' in struct '%s' at %d
        WARN_CR_BADOFF           # 32 CONTAINING_RECORD: too small offset %d for struct '%s'
        WARN_BAD_STROFF          # 33 user specified stroff has not been processed: %s
        WARN_BAD_VARSIZE         # 34 inconsistent variable size for '%s'
        WARN_UNSUPP_REG          # 35 unsupported processor register '%s'
        WARN_UNALIGNED_ARG       # 36 unaligned function argument '%s'
        WARN_BAD_STD_TYPE        # 37 corrupted or unexisting local type '%s'
        WARN_BAD_CALL_SP         # 38 bad sp value at call
        WARN_MISSED_SWITCH       # 39 wrong markup of switch jump, skipped it
        WARN_BAD_SP              # 40 positive sp value %a has been found
        WARN_BAD_STKPNT          # 41 wrong sp change point
        WARN_UNDEF_LVAR          # 42 variable '%s' is possibly undefined
        WARN_JUMPOUT             # 43 control flows out of bounds
        WARN_BAD_VALRNG          # 44 values range analysis failed
        WARN_BAD_SHADOW          # 45 ignored the value written to the shadow area of the succeeding call
        WARN_OPT_VALRNG          # 46 conditional instruction was optimized away because %s
        WARN_RET_LOCREF          # 47 returning address of temporary local variable '%s'
        WARN_BAD_MAPDST          # 48 too short map destination '%s' for variable '%s'
        WARN_BAD_INSN            # 49 bad instruction
        WARN_ODD_ABI             # 50 encountered odd instruction for the current ABI
        WARN_UNBALANCED_STACK    # 51 unbalanced stack, ignored a potential tail call
        WARN_OPT_VALRNG2         # 52 mask 0x%X is shortened because %s <= 0x%X"
        WARN_OPT_VALRNG3         # 53 masking with 0X%X was optimized away because %s <= 0x%X
        WARN_OPT_USELESS_JCND    # 54 simplified comparisons for '%s': %s became %s
        WARN_SUBFRAME_OVERFLOW   # 55 call arguments overflow the function chunk frame
        WARN_MAX                 # may be used in notes as a placeholder when the
                                 # warning id is not available

    # Warning instances
    cdef cppclass hexwarn_t:
        ea_t ea        #< Address where the warning occurred
        warnid_t id    #< Warning id
        qstring text   #< Fully formatted text of the warning

    ctypedef qvector[hexwarn_t] hexwarns_t

    #-------------------------------------------------------------------------
    # Microcode maturity levels
    cpdef enum class mba_maturity_t:
        MMAT_ZERO = 0         # microcode does not exist
        MMAT_GENERATED = 1    # generated microcode
        MMAT_PREOPTIMIZED = 2 # preoptimized pass is complete
        MMAT_LOCOPT = 3       # local optimization of each basic block is complete.
                              # control flow graph is ready too.
        MMAT_CALLS = 4        # detected call arguments. see also hxe_calls_done
        MMAT_GLBOPT1 = 5      # performed the first pass of global optimization
        MMAT_GLBOPT2 = 6      # most global optimization passes are done
        MMAT_GLBOPT3 = 7      # completed all global optimization. microcode is fixed now.
        MMAT_LVARS = 8        # allocated local variables


    # -------------------------------------------------------------------------
    # Ranges to decompile. Either a function or an explicit vector of ranges.
    cdef cppclass mba_ranges_t:
        func_t *pfn           # function to decompile. if not null, then function mode.
        rangevec_t ranges     # snippet mode: ranges to decompile.
                              # functions mode


    cdef cppclass mba_t:
        """
        Array of micro blocks representing microcode for a decompiled function.
        The first micro block is the entry point, the last one is the exit point.
        The entry and exit blocks are always empty. The exit block is generated
        at MMAT_LOCOPT maturity level.
        """

        # flags for the mba_t
        uint32 flags   # this is private in the original code
        uint32 flags2  # this is private in the original code

        # Various flag-checking methods
        bint precise_defeas() const
        bint optimized() const
        bint short_display() const
        bint show_reduction() const
        bint graph_insns() const
        bint loaded_gdl() const
        bint should_beautify() const
        bint rtype_refined() const
        bint may_refine_rettype() const
        bint use_wingraph32() const
        bint display_numaddrs() const
        bint display_valnums() const
        bint is_pattern() const
        bint is_thunk() const
        bint saverest_done() const
        bint callinfo_built() const
        bint really_alloc() const
        bint lvars_allocated() const
        bint chain_varnums_ok() const
        bint returns_fpval() const
        bint has_passregs() const
        bint generated_asserts() const
        bint propagated_asserts() const
        bint deleted_pairs() const
        bint common_stkvars_stkargs() const
        bint lvar_names_ok() const
        bint lvars_renamed() const
        bint has_over_chains() const
        bint valranges_done() const
        bint argidx_ok() const
        bint argidx_sorted() const
        bint code16_bit_removed() const
        bint has_stack_retval() const
        bint has_outlines() const
        bint is_ctr() const
        bint is_dtr() const
        bint is_cdtr() const
        bint prop_complex() const
        int get_mba_flags() const
        int get_mba_flags2() const
        void set_mba_flags(int f)
        void clr_mba_flags(int f)
        void set_mba_flags2(int f)
        void clr_mba_flags2(int f)
        void clr_cdtr()
        int calc_shins_flags() const

        #
        #                      +-----------+ <- inargtop
        #                      |   prmN    |
        #                      |   ...     | <- minargref
        #                      |   prm0    |
        #                      +-----------+ <- inargoff
        #                      |shadow_args|
        #                      +-----------+
        #                      |  retaddr  |
        #      frsize+frregs   +-----------+ <- initial esp  |
        #                      |  frregs   |                 |
        #            +frsize   +-----------+ <- typical ebp  |
        #                      |           |  |              |
        #                      |           |  | fpd          |
        #                      |           |  |              |
        #                      |  frsize   | <- current ebp  |
        #                      |           |                 |
        #                      |           |                 |
        #                      |           |                 | stacksize
        #                      |           |                 |
        #                      |           |                 |
        #                      |           | <- minstkref    |
        #  stkvar base off 0   +---..      |                 |    | current
        #                      |           |                 |    | stack
        #                      |           |                 |    | pointer
        #                      |           |                 |    | range
        #                      |tmpstk_size|                 |    | (what getspd() returns)
        #                      |           |                 |    |
        #                      |           |                 |    |
        #                      +-----------+ <- minimal sp   |    | offset 0 for the decompiler (vd)
        #
        # There is a detail that may add confusion when working with stack variables.
        # The decompiler does not use the same stack offsets as IDA.
        # The picture above should explain the difference:
        # - IDA stkoffs are displayed on the left, decompiler stkoffs - on the right
        # - Decompiler stkoffs are always >= 0
        # - IDA stkoff==0 corresponds to stkoff==tmpstk_size in the decompiler
        # - See stkoff_vd2ida and stkoff_ida2vd below to convert IDA stkoffs to vd stkoff

        # Convert a stack offset used in vd to a stack offset used in ida stack frame
        sval_t stkoff_vd2ida(sval_t off) const

        # Convert a ida stack frame offset to a stack offset used in vd
        sval_t stkoff_ida2vd(sval_t off) const
        sval_t argbase() const

        # Stack argument check
        bint is_stkarg(const lvar_t &v) const

        ssize_t get_stkvar(
            udm_t *udm,
            sval_t vd_stkoff,
            uval_t *p_idaoff = NULL,
            tinfo_t *p_frame = NULL) const

        argloc_t get_ida_argloc(const lvar_t &v) const

        # Data members
        mba_ranges_t mbr
        ea_t entry_ea
        ea_t last_prolog_ea
        ea_t first_epilog_ea
        int qty                  #< number of basic blocks
        int npurged              #< -1 - unknown
        cm_t cc                  #< calling convention
        sval_t tmpstk_size       #< size of the temporary stack part
                                 #< (which dynamically changes with push/pops)
        sval_t frsize            #< size of local stkvars range in the stack frame
        sval_t frregs            #< size of saved registers range in the stack frame
        sval_t fpd               #< frame pointer delta
        int pfn_flags            #< copy of func_t::flags
        int retsize              #< size of return address in the stack frame
        int shadow_args          #< size of shadow argument area
        sval_t fullsize          #< Full stack size including incoming args
        sval_t stacksize         #: The maximal size of the function stack including
                                 #: bytes allocated for outgoing call arguments
                                 #: (up to retaddr)
        sval_t inargoff          #: offset of the first stack argument;
                                 #: after fix_scattered_movs() INARGOFF may
                                 #: be less than STACKSIZE
        sval_t minstkref         #: The lowest stack location whose address was taken
        ea_t minstkref_ea        #: address with lowest minstkref (for debugging)
        sval_t minargref         #: The lowest stack argument location whose address was taken
                                 #: This location and locations above it can be aliased
                                 #: It controls locations >= inargoff-shadow_args
        sval_t spd_adjust        #: If sp>0, the max positive sp value
        ivlset_t gotoff_stkvars  #: stkvars that hold .got offsets. considered to be unaliasable
        ivlset_t restricted_memory
        ivlset_t aliased_memory  #: aliased_memory+restricted_memory=ALLMEM
        mlist_t nodel_memory     #: global dead elimination may not delete references to this area
        rlist_t consumed_argregs #: registers converted into stack arguments, should not be used as arguments

        mba_maturity_t maturity  #: current maturity level
        mba_maturity_t reqmat    #: required maturity level

        bint final_type          #: is the function type final? (specified by the user)
        tinfo_t idb_type         #: function type as retrieved from the database
        reginfovec_t idb_spoiled #: MBA_SPLINFO && final_type: info in ida format
        mlist_t spoiled_list     #: MBA_SPLINFO && !final_type: info in vd format
        int fti_flags            #: FTI_... constants for the current function

        qstring label             #: name of the function or pattern (colored)
        lvars_t vars              #: local variables
        intvec_t argidx           #: input arguments (indexes into 'vars')
        int retvaridx             #: index of variable holding the return value
                                  #: -1 means none

        ea_t error_ea             #: during microcode generation holds ins.ea
        qstring error_strarg

        mblock_t* blocks          #: double linked list of blocks
        mblock_t** natural        #: natural order of blocks

        ivl_with_name_t[6] std_ivls #: we treat memory as consisting of 6 parts
                                    #: see \ref memreg_index_t

        # 'mutable' is a C++ keyword, not needed in Cython
        hexwarns_t notes
        uchar[32] occurred_warns  # occurred warning messages

         # Warning checks
        # Was a write to a constant detected?
        bint write_to_const_detected() const

        # Was a bad call stack pointer detected?
        bint bad_call_sp_detected() const

        # Are register arguments not aligned?
        bint regargs_is_not_aligned() const

        # Does this have a bad stack pointer?
        bint has_bad_sp() const

        char reserved[]

        void term()
        # Get the current function.
        func_t *get_curfunc() const

        # Does this use a frame?
        bint use_frame() const

        # Does the range contain the given address?
        bint range_contains(ea_t ea) const

        # Is this a snippet?
        bint is_snippet() const

        # Set maturity level.
        # \param mat new maturity level
        # \return true if it is time to stop analysis
        # Plugins may use this function to skip some parts of the analysis.
        # The maturity level cannot be decreased.
        bint set_maturity(mba_maturity_t mat)

        # Optimize each basic block locally
        # \param locopt_bits combination of \ref LOCOPT_ bits
        # \return number of changes. 0 means nothing changed
        # This function is called by the decompiler, usually there is no need to
        # call it explicitly.
        int optimize_local(int locopt_bits)

        # Build control flow graph.
        # This function may be called only once. It calculates the type of each
        # basic block and the adjacency list. optimize_local() calls this function
        # if necessary. You need to call this function only before MMAT_LOCOPT.
        # \return error code
        merror_t build_graph()

        # Get control graph.
        # Call build_graph() if you need the graph before MMAT_LOCOPT.
        # mbl_graph_t *get_graph()

        # Analyze calls and determine calling conventions.
        # \param acflags permitted actions that are necessary for successful detection
        #                of calling conventions. See \ref ACFL_
        # \return number of calls. -1 means error.
        int analyze_calls(int acflags)

        # Optimize microcode globally.
        # This function applies various optimization methods until we reach the
        # fixed point. After that it preallocates lvars unless reqmat forbids it.
        # \return error code
        # merror_t optimize_global()

        # Allocate local variables.
        # Must be called only immediately after optimize_global(), with no
        # modifications to the microcode. Converts registers,
        # stack variables, and similar operands into mop_l. This call will not fail
        # because all necessary checks were performed in optimize_global().
        # After this call the microcode reaches its final state.
        void alloc_lvars()

        # Dump microcode to a file.
        # The file will be created in the directory pointed by IDA_DUMPDIR envvar.
        # Dump will be created only if IDA is run under debugger.
        void dump() const
        void vdump_mba(bint _verify, const char *title, va_list va) const
        void dump_mba(bint _verify, const char *title, ...) const

        # Print microcode to any destination.
        # \param vp print sink
        # void print(vd_printer_t &vp) const

        # Verify microcode consistency.
        # \param always if false, the check will be performed only if ida runs
        #               under debugger
        # If any inconsistency is discovered, an internal error will be generated.
        # We strongly recommend you to call this function before returing control
        # to the decompiler from your callbacks, in the case if you modified
        # the microcode. If the microcode is inconsistent, this function will
        # generate an internal error. We provide the source code of this function
        # in the plugins/hexrays_sdk/verifier directory for your reference.
        void verify(bint always) const

        # Mark the microcode use-def chains dirty.
        # Call this function if any inter-block data dependencies got changed
        # because of your modifications to the microcode. Failing to do so may
        # cause an internal error.
        void mark_chains_dirty()

        # Get basic block by its serial number.
        mblock_t *get_mblock(uint n)

        # Insert a block in the middle of the mbl array.
        # The very first block of microcode must be empty, it is the entry block.
        # The very last block of microcode must be BLT_STOP, it is the exit block.
        # Therefore inserting a new block before the entry point or after the exit
        # block is not a good idea.
        # \param bblk the new block will be inserted before BBLK
        # \return ptr to the new block
        mblock_t *insert_block(int bblk)

        # Split a block: insert a new one after the block, move some instructions
        # to new block
        # \param blk        block to be split
        # \param start_insn all instructions to be moved to new block: starting with this one up to the end
        # \return ptr to the new block
        mblock_t *split_block(mblock_t *blk, minsn_t *start_insn)

        # Delete a block.
        # \param blk block to delete
        # \return true if at least one of the other blocks became empty or unreachable
        bint remove_block(mblock_t *blk)
        bint remove_blocks(int start_blk, int end_blk)

        # Make a copy of a block.
        # This function makes a simple copy of the block. It does not fix the
        # predecessor and successor lists, they must be fixed if necessary.
        # \param blk         block to copy
        # \param new_serial  position of the copied block
        # \param cpblk_flags combination of \ref CPBLK_... bits
        # \return pointer to the new copy
        mblock_t *copy_block(mblock_t *blk, int new_serial, int cpblk_flags)

        # Delete all empty and unreachable blocks.
        # Blocks marked with MBL_KEEP won't be deleted.
        bint remove_empty_and_unreachable_blocks()

        # Merge blocks.
        # This function merges blocks constituting linear flow.
        # It calls remove_empty_and_unreachable_blocks() as well.
        # \return true if changed any blocks
        bint merge_blocks()

        # Visit all operands of all instructions.
        # \param mv operand visitor
        # \return non-zero value returned by mv.visit_mop() or zero
        #int for_all_ops(mop_visitor_t &mv)

        # Visit all instructions.
        # This function visits all instruction and subinstructions.
        # \param mv instruction visitor
        # \return non-zero value returned by mv.visit_mop() or zero
        # int for_all_insns(minsn_visitor_t &mv)

        # Visit all top level instructions.
        # \param mv instruction visitor
        # \return non-zero value returned by mv.visit_mop() or zero
        # int for_all_topinsns(minsn_visitor_t &mv)

        # Find an operand in the microcode.
        # This function tries to find the operand that matches LIST.
        # Any operand that overlaps with LIST is considered as a match.
        # \param[out] ctx context information for the result
        # \param ea       desired address of the operand. BADADDR means to accept any address.
        # \param is_dest  search for destination operand? this argument may be
        #                 ignored if the exact match could not be found
        # \param list     list of locations the correspond to the operand
        # \return pointer to the operand or nullptr.
        # mop_t *find_mop(op_parent_info_t *ctx, ea_t ea, bint is_dest, const mlist_t &list)

        # Create a call of a helper function.
        # \param ea       The desired address of the instruction
        # \param helper   The helper name
        # \param rettype  The return type (nullptr or empty type means 'void')
        # \param callargs The helper arguments (nullptr-no arguments)
        # \param out      The operand where the call result should be stored.
        #                 If this argument is not nullptr, "mov helper_call(), out"
        #                 will be generated. Otherwise "call helper()" will be
        #                 generated. Note: the size of this operand must be equal
        #                 to the RETTYPE size
        # \return pointer to the created instruction or nullptr if error
        minsn_t *create_helper_call(
            ea_t ea,
            const char *helper,
            const tinfo_t *rettype = NULL,
            const mcallargs_t *callargs = NULL,
            const mop_t *out = NULL)

        # Prepare the lists of registers & memory that are defined/killed by a
        # function
        # \param[out] return_regs  defined regs to return (eax,edx)
        # \param[out] spoiled      spoiled regs (flags,ecx,mem)
        # \param      type         the function type
        # \param      call_ea      the call insn address (if known)
        # \param      tail_call    is it the tail call?
        void get_func_output_lists(
            mlist_t *return_regs,
            mlist_t *spoiled,
            const tinfo_t &type,
            ea_t call_ea = BADADDR,
            bint tail_call = False)

        # Get input argument of the decompiled function.
        # \param n argument number (0..nargs-1)
        lvar_t &arg(int n)
        const lvar_t &arg(int n) const

        # Allocate a fictional address.
        # This function can be used to allocate a new unique address for a new
        # instruction, if re-using any existing address leads to conflicts.
        # For example, if the last instruction of the function modifies R0
        # and falls through to the next function, it will be a tail call:
        #    LDM R0!, {R4,R7}
        #    end of the function
        #    start of another function
        # In this case R0 generates two different lvars at the same address:
        #   - one modified by LDM
        #   - another that represents the return value from the tail call
        #
        # Another example: a third-party plugin makes a copy of an instruction.
        # This may lead to the generation of two variables at the same address.
        # Example 3: fictional addresses can be used for new instructions created
        # while modifying the microcode.
        # This function can be used to allocate a new unique address for a new
        # instruction or a variable.
        # The fictional address is selected from an unallocated address range.
        # \param real_ea real instruction address (BADADDR is ok too)
        # \return a unique fictional address
        ea_t alloc_fict_ea(ea_t real_ea)

        # Resolve a fictional address.
        # This function provides a reverse of the mapping made by alloc_fict_ea().
        # \param fict_ea fictional definition address
        # \return the real instruction address
        ea_t map_fict_ea(ea_t fict_ea) const

        # Get information about various memory regions.
        # We map the stack frame to the global memory, to some unused range.
        # const ivl_t &get_std_region(memreg_index_t idx) const
        # const ivl_t &get_lvars_region() const
        # const ivl_t &get_shadow_region() const
        # const ivl_t &get_args_region() const
        # ivl_t get_stack_region() const

        # Serialize mbl array into a sequence of bytes.
        void serialize(bytevec_t &vout) const

        # Deserialize a byte sequence into mbl array.
        # \param bytes pointer to the beginning of the byte sequence.
        # \param nbytes number of bytes in the byte sequence.
        # \return new mbl array
        @staticmethod
        mba_t *deserialize(const uchar *bytes, size_t nbytes)

        # Create and save microcode snapshot
        void save_snapshot(const char *description)

        # Allocate a kernel register.
        # \param size size of the register in bytes
        # \param check_size if true, only the sizes that correspond to a size of
        #                   a basic type will be accepted.
        # \return allocated register. mr_none means failure.
        mreg_t alloc_kreg(size_t size, bint check_size = True)

        # Free a kernel register.
        # If wrong arguments are passed, this function will generate an internal error.
        # \param reg a previously allocated kernel register
        # \param size size of the register in bytes
        void free_kreg(mreg_t reg, size_t size)

        # \defgroup INLINE_ inline_func() flags
        #define INLINE_EXTFRAME 0x0001 # Inlined function has its own (external) frame
        #define INLINE_DONTCOPY 0x0002 # Do not reuse old inlined copy even if it exists

        # Inline a range.
        # Currently only functions are supported, not arbitrary ranges.
        # This function may be called only during the initial microcode generation phase.
        # \param cdg the codegenerator object
        # \param blknum the block contaning the call/jump instruction to inline
        # \param ranges the set of ranges to inline
        # \param decomp_flags combination of \ref DECOMP_ bits
        # \param inline_flags combination of \ref INLINE_ bits
        # \return error code
        # merror_t inline_func(
        #     codegen_t &cdg,
        #     int blknum,
        #     mba_ranges_t &ranges,
        #     int decomp_flags = 0,
        #     int inline_flags = 0)

        # Find a sp change point.
        # returns stkpnt p, where p->ea <= ea
        # const stkpnt_t *locate_stkpnt(ea_t ea) const

        bint set_lvar_name(lvar_t &v, const char *name, int flagbits)
        bint set_nice_lvar_name(lvar_t &v, const char *name)
        bint set_user_lvar_name(lvar_t &v, const char *name)

    # --- Standalone SDK functions ---
    cdef int get_mreg_name(qstring *out, mreg_t reg, int width, void *ud)

cdef enum LOCOPT_FLAGS:
    LOCOPT_ALL     = 0x0001  # redo optimization for all blocks. if this bit is not set, only dirty blocks will be optimized
    LOCOPT_REFINE  = 0x0002  # refine return type, ok to fail
    LOCOPT_REFINE2 = 0x0004  # refine return type, try harder

cdef enum OPERAND_PROPERTIES:
    OPROP_IMPDONE = 0x01   # imported operand (a pointer) has been dereferenced
    OPROP_UDT     = 0x02   # a struct or union
    OPROP_FLOAT   = 0x04   # possibly floating value
    OPROP_CCFLAGS = 0x08   # mop_n: a pc-relative value
                           # mop_a: an address obtained from a relocation
                           # else: value of a condition code register (like mr_cc)
    OPROP_UDEFVAL = 0x10   # uses undefined value
    OPROP_LOWADDR = 0x20   # a low address offset

# Apparently, cannot initialize a Cython enum with extern constants.
cdef enum MOPT:
    ZERO          =  0   # none
    REGISTER      =  1   # register (they exist until MMAT_LVARS)
    NUMBER        =  2   # immediate number constant
    STRING        =  3   # immediate string constant (user representation)
    DEST_RESULT   =  4   # result of another instruction
    STACK         =  5   # local stack variable (they exist until MMAT_LVARS)
    GLOBAL        =  6   # global variable
    MBLOCK        =  7   # micro basic block (mblock_t)
    ARGUMENT_LIST =  8   # list of arguments
    LOCAL         =  9   # local variable
    ADDRESS       = 10   # mop_addr_t: address of operand (mop_l, mop_v, mop_S, mop_r)
    HELPER        = 11   # helper function
    CASES         = 12   # mcases
    FLOAT         = 13   # floating point constant
    PAIR          = 14   # operand pair
    SCATTERED     = 15   # scattered

ctypedef mop_t* mop_t_ptr
ctypedef shared_ptr[mop_t] shared_mop_t_ptr
ctypedef pair[mop_t_ptr, uint64] mop_off_pair_t
# Store propagated constants as 64-bit unsigned to avoid overflow
ctypedef pair[uint64, int] const_val_t
ctypedef map[qstring, const_val_t] CppConstMap



# Declare the public function from our .pyx file
cpdef run_dataflow_cython(object mba_py)


# cpdef enum class OPROP_FLAGS(unsigned int):
#     OPROP_IMPDONE  = 0x01 # imported operand (a pointer) has been dereferenced
#     OPROP_UDT      = 0x02 # a struct or union
#     OPROP_FLOAT    = 0x04 # possibly floating value
#     OPROP_CCFLAGS  = 0x08 # mop_n: a pc-relative value
#                             # mop_a: an address obtained from a relocation
#                             # else: value of a condition code register (like mr_cc)
#     OPROP_UDEFVAL  = 0x10 # uses undefined value
#     OPROP_LOWADDR  = 0x20 # a low address offset

# cpdef enum class MBL_FLAGS(unsigned int):
#     MBL_PRIV        = 0x0001   # private block - no instructions except
#                                 # the specified are accepted (used in patterns)
#     MBL_NONFAKE     = 0x0000   # regular block
#     MBL_FAKE        = 0x0002   # fake block
#     MBL_GOTO        = 0x0004   # this block is a goto target
#     MBL_TCAL        = 0x0008   # artificial call block for tail calls
#     MBL_PUSH        = 0x0010   # needs "convert push/pop instructions"
#     MBL_DMT64       = 0x0020   # needs "demote 64bits"
#     MBL_COMB        = 0x0040   # needs "combine" pass
#     MBL_PROP        = 0x0080   # needs 'propagation' pass
#     MBL_DEAD        = 0x0100   # needs "eliminate deads" pass
#     MBL_LIST        = 0x0200   # use/def lists are ready (not dirty)
#     MBL_INCONST     = 0x0400   # inconsistent lists: we are building them
#     MBL_CALL        = 0x0800   # call information has been built
#     MBL_BACKPROP    = 0x1000   # performed backprop_cc
#     MBL_NORET       = 0x2000   # dead end block: doesn't return execution control
#     MBL_DSLOT       = 0x4000   # block for delay slot
#     MBL_VALRANGES   = 0x8000   # should optimize using value ranges
#     MBL_KEEP        = 0x10000  # do not remove even if unreachable
#     MBL_INLINED     = 0x20000  # block was inlined, not originally part of mbr
#     MBL_EXTFRAME    = 0x40000  # an inlined block with an external frame


# /// \defgroup CVAR_ Local variable property bits
# /// Used in lvar_t::flags
# ///@{
# #define CVAR_USED    0x00000001 ///< is used in the code?
# #define CVAR_TYPE    0x00000002 ///< the type is defined?
# #define CVAR_NAME    0x00000004 ///< has nice name?
# #define CVAR_MREG    0x00000008 ///< corresponding mregs were replaced?
# #define CVAR_NOWD    0x00000010 ///< width is unknown
# #define CVAR_UNAME   0x00000020 ///< user-defined name
# #define CVAR_UTYPE   0x00000040 ///< user-defined type
# #define CVAR_RESULT  0x00000080 ///< function result variable
# #define CVAR_ARG     0x00000100 ///< function argument
# #define CVAR_FAKE    0x00000200 ///< fake variable (return var or va_list)
# #define CVAR_OVER    0x00000400 ///< overlapping variable
# #define CVAR_FLOAT   0x00000800 ///< used in a fpu insn
# #define CVAR_SPOILED 0x00001000 ///< internal flag, do not use: spoiled var
# #define CVAR_MAPDST  0x00002000 ///< other variables are mapped to this var
# #define CVAR_PARTIAL 0x00004000 ///< variable type is partialy defined
# #define CVAR_THISARG 0x00008000 ///< 'this' argument of c++ member functions
# #define CVAR_SPLIT   0x00010000 ///< variable was created by an explicit request
#                                 ///< otherwise we could reuse an existing var
# #define CVAR_REGNAME 0x00020000 ///< has a register name (like _RAX): if lvar
#                                 ///< is used by an m_ext instruction
# #define CVAR_NOPTR   0x00040000 ///< variable cannot be a pointer (user choice)
# #define CVAR_DUMMY   0x00080000 ///< dummy argument (added to fill a hole in
#                                 ///< the argument list)
# #define CVAR_NOTARG  0x00100000 ///< variable cannot be an input argument
# #define CVAR_AUTOMAP 0x00200000 ///< variable was automatically mapped
# #define CVAR_BYREF   0x00400000 ///< the address of the variable was taken
# #define CVAR_INASM   0x00800000 ///< variable is used in instructions translated
#                                 ///< into __asm {...}
# #define CVAR_UNUSED  0x01000000 ///< user-defined __unused attribute
#                                 ///< meaningful only if: is_arg_var() && !mba->final_type
# #define CVAR_SHARED  0x02000000 ///< variable is mapped to several chains
# #define CVAR_SCARG   0x04000000 ///< variable is a stack argument that was
#                                 ///< transformed from a scattered one
# ///@}


# Function flags (used by func_t::flags)
# FUNC_NORET: Function doesn't return
# FUNC_FAR: Far function
# FUNC_LIB: Library function
# FUNC_STATICDEF: Static function
# FUNC_FRAME: Function uses frame pointer (BP)
# FUNC_USERFAR: User has specified far-ness of the function
# FUNC_HIDDEN: A hidden function chunk
# FUNC_THUNK: Thunk (jump) function
# FUNC_BOTTOMBP: BP points to the bottom of the stack frame
# FUNC_NORET_PENDING: Function 'non-return' analysis must be performed.
# FUNC_SP_READY: SP-analysis has been performed.
# FUNC_FUZZY_SP: Function changes SP in untraceable way, e.g. and esp, 0FFFFFFF0h
# FUNC_PROLOG_OK: Prolog analysis has been performed by last SP-analysis
# FUNC_PURGED_OK: 'argsize' field has been validated.
# FUNC_TAIL: This is a function tail. Other bits must be clear (except FUNC_HIDDEN).
# FUNC_LUMINA: Function info is provided by Lumina.
# FUNC_OUTLINE: Outlined code, not a real function.
# FUNC_REANALYZE: Function frame changed, request to reanalyze after last insn.
# FUNC_UNWIND: function is an exception unwind handler
# FUNC_CATCH: function is an exception catch handler
# FUNC_RESERVED: Reserved (for internal usage)
# (These are #define constants in C++; define them in .pxd as needed in Python.)
