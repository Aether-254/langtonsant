import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1341 : checkSingleBlackFast (-14, 13) 10891 .east (-3, -7) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
