import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1317 : checkSingleBlackFast (-12, 15) 11727 .east (-1, -6) (-25, -21) = true := by
  decide +kernel

end LangtonsAnt
