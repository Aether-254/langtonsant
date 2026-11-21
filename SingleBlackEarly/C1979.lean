import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1979 : checkSingleBlackFast (-72, -49) 14991 .west (23, 33) (-52, 13) = true := by
  decide +kernel

end LangtonsAnt
