import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1507 : checkSingleBlackFast (-25, -7) 10760 .north (2, 0) (-28, -4) = true := by
  decide +kernel

end LangtonsAnt
