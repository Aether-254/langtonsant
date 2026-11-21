import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0845 : checkSingleBlackFast (-4, 8) 19445 .west (-12, 8) (-28, -23) = true := by
  decide +kernel

end LangtonsAnt
