import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1953 : checkSingleBlackFast (-71, -43) 25321 .east (31, 19) (9, -54) = true := by
  decide +kernel

end LangtonsAnt
