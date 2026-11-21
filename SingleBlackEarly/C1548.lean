import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1548 : checkSingleBlackFast (-30, -12) 27279 .east (5, -5) (-14, -27) = true := by
  decide +kernel

end LangtonsAnt
