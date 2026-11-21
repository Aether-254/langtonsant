import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1037 : checkSingleBlackFast (-12, 4) 19708 .south (-12, -4) (-30, -12) = true := by
  decide +kernel

end LangtonsAnt
