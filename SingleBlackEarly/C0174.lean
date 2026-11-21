import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0174 : checkSingleBlackFast (-7, 7) 27957 .west (-13, 0) (-20, -42) = true := by
  decide +kernel

end LangtonsAnt
