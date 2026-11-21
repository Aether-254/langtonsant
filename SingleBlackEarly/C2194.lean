import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2194 : checkSingleBlackFast (-93, -66) 20498 .north (38, 31) (-65, -44) = true := by
  decide +kernel

end LangtonsAnt
