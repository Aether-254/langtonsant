import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2163 : checkSingleBlackFast (-86, -67) 22272 .north (45, 41) (-71, -33) = true := by
  decide +kernel

end LangtonsAnt
