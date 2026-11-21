import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1517 : checkSingleBlackFast (-30, -7) 12807 .west (2, 12) (-31, -8) = true := by
  decide +kernel

end LangtonsAnt
